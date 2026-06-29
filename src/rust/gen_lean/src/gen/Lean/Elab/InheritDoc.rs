// Lean compiler output
// Module: Lean.Elab.InheritDoc
// Imports: Lean.Elab.InfoTree.Main
use crate::ffi::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_name_eq, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Attributes::{
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::CoreM::l_Lean_Elab_inServer;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::Extension::{
    l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt, l_Lean_addBuiltinDocString,
    l_Lean_findInternalDocString_x3f, l_Lean_findSimpleDocString_x3f,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed,
    runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 99, 121, 99, 108, 101, 32, 100, 101, 116, 101, 99, 116, 101, 100, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 97, 108, 114, 101, 97, 100, 121, 32, 104, 97, 115, 32, 97, 110, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [32, 97, 108, 114, 101, 97, 100, 121, 32, 104, 97, 115, 32, 97, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 58, 32, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 105, 110, 102, 101, 114, 32, 100, 111, 99, 32, 115, 111, 117, 114, 99, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [73, 110, 104, 101, 114, 105, 116, 68, 111, 99, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16523336232899777337 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3361983042095182364 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9588181330932994109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9935067116431792180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2937937637890837981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1913205937357475176 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,13727712315849183762 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17495018376186380235 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 986682242 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9754258626469971871 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12835772358407075316 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18022824350782341408 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1147403744356159889 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11976168950125103187 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [105, 110, 104, 101, 114, 105, 116, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<139> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 139, m_capacity: 139, m_length: 138, m_data: [85, 115, 101, 115, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 10, 10, 96, 64, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 32, 100, 101, 99, 108, 93, 96, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 110, 104, 101, 114, 105, 116, 32, 116, 104, 101, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 100, 101, 99, 108, 96, 46, 10, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(
    mut v_opts_1232_: *mut crate::leanh::LeanObject,
    mut v_opt_1233_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1234_ = crate::leanh::lean_ctor_get(v_opt_1233_, 0);
    v_defValue_1235_ = crate::leanh::lean_ctor_get(v_opt_1233_, 1);
    v_map_1236_ = crate::leanh::lean_ctor_get(v_opts_1232_, 0);
    v___x_1237_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1236_,
            v_name_1234_,
        );
    if crate::leanh::lean_obj_tag(v___x_1237_) == 0 {
        let mut v___x_1238_: u8 = 0;
        v___x_1238_ = (crate::leanh::lean_unbox(v_defValue_1235_) as u8);
        return v___x_1238_;
    } else {
        let mut v_val_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1239_ = crate::leanh::lean_ctor_get(v___x_1237_, 0);
        crate::leanh::lean_inc(v_val_1239_);
        crate::leanh::lean_dec_ref_known(v___x_1237_, 1);
        if crate::leanh::lean_obj_tag(v_val_1239_) == 1 {
            let mut v_v_1240_: u8 = 0;
            v_v_1240_ = crate::leanh::lean_ctor_get_uint8(v_val_1239_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1239_, 0);
            return v_v_1240_;
        } else {
            let mut v___x_1241_: u8 = 0;
            crate::leanh::lean_dec(v_val_1239_);
            v___x_1241_ = (crate::leanh::lean_unbox(v_defValue_1235_) as u8);
            return v___x_1241_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5___boxed(
    mut v_opts_1242_: *mut crate::leanh::LeanObject,
    mut v_opt_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: u8 = 0;
    let mut v_r_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(v_opts_1242_, v_opt_1243_);
    crate::leanh::lean_dec_ref(v_opt_1243_);
    crate::leanh::lean_dec_ref(v_opts_1242_);
    v_r_1245_ = crate::leanh::lean_box((v_res_1244_) as usize);
    return v_r_1245_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1246_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_1248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1250_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1251_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    crate::leanh::lean_ctor_set(v___x_1251_, 1, v___x_1250_);
    crate::leanh::lean_ctor_set(v___x_1251_, 2, v___x_1250_);
    crate::leanh::lean_ctor_set(v___x_1251_, 3, v___x_1250_);
    crate::leanh::lean_ctor_set(v___x_1251_, 4, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1251_, 5, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1251_, 6, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1251_, 7, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1251_, 8, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1251_, 9, v___x_1249_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1253_ = lean_mk_empty_array_with_capacity(v___x_1252_);
    v___x_1254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1254_, 0, v___x_1253_);
    return v___x_1254_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = 5usize;
    v___x_1256_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1257_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
    v___x_1259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_1260_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1260_, 0, v___x_1259_);
    crate::leanh::lean_ctor_set(v___x_1260_, 1, v___x_1258_);
    crate::leanh::lean_ctor_set(v___x_1260_, 2, v___x_1256_);
    crate::leanh::lean_ctor_set(v___x_1260_, 3, v___x_1256_);
    crate::leanh::lean_ctor_set_usize(v___x_1260_, 4, v___x_1255_);
    return v___x_1260_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = crate::leanh::lean_box(1);
    v___x_1262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_1263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1264_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1262_);
    crate::leanh::lean_ctor_set(v___x_1264_, 2, v___x_1261_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = lean_st_ref_get(v___y_1267_);
    v_env_1270_ = crate::leanh::lean_ctor_get(v___x_1269_, 0);
    crate::leanh::lean_inc_ref(v_env_1270_);
    crate::leanh::lean_dec(v___x_1269_);
    v_options_1271_ = crate::leanh::lean_ctor_get(v___y_1266_, 2);
    v___x_1272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_1273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_1271_);
    v___x_1274_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1274_, 0, v_env_1270_);
    crate::leanh::lean_ctor_set(v___x_1274_, 1, v___x_1272_);
    crate::leanh::lean_ctor_set(v___x_1274_, 2, v___x_1273_);
    crate::leanh::lean_ctor_set(v___x_1274_, 3, v_options_1271_);
    v___x_1275_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
    crate::leanh::lean_ctor_set(v___x_1275_, 1, v_msgData_1265_);
    v___x_1276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1277_, v___y_1278_, v___y_1279_);
    crate::leanh::lean_dec(v___y_1279_);
    crate::leanh::lean_dec_ref(v___y_1278_);
    return v_res_1281_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0(
    mut v___y_1290_: u8,
    mut v_suppressElabErrors_1291_: u8,
    mut v_x_1292_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1292_) == 1 {
        let mut v_pre_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1293_ = crate::leanh::lean_ctor_get(v_x_1292_, 0);
        match crate::leanh::lean_obj_tag(v_pre_1293_) {
            1 => {
                let mut v_pre_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_1294_ = crate::leanh::lean_ctor_get(v_pre_1293_, 0);
                match crate::leanh::lean_obj_tag(v_pre_1294_) {
                    0 => {
                        let mut v_str_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1298_: u8 = 0;
                        v_str_1295_ = crate::leanh::lean_ctor_get(v_x_1292_, 1);
                        v_str_1296_ = crate::leanh::lean_ctor_get(v_pre_1293_, 1);
                        v___x_1297_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0;
                        v___x_1298_ = lean_string_dec_eq(v_str_1296_, v___x_1297_);
                        if v___x_1298_ == 0 {
                            let mut v___x_1299_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1300_: u8 = 0;
                            v___x_1299_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1;
                            v___x_1300_ = lean_string_dec_eq(v_str_1296_, v___x_1299_);
                            if v___x_1300_ == 0 {
                                return v___y_1290_;
                            } else {
                                let mut v___x_1301_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1302_: u8 = 0;
                                v___x_1301_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2;
                                v___x_1302_ = lean_string_dec_eq(v_str_1295_, v___x_1301_);
                                if v___x_1302_ == 0 {
                                    return v___y_1290_;
                                } else {
                                    return v_suppressElabErrors_1291_;
                                }
                            }
                        } else {
                            let mut v___x_1303_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1304_: u8 = 0;
                            v___x_1303_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3;
                            v___x_1304_ = lean_string_dec_eq(v_str_1295_, v___x_1303_);
                            if v___x_1304_ == 0 {
                                return v___y_1290_;
                            } else {
                                return v_suppressElabErrors_1291_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1305_ = crate::leanh::lean_ctor_get(v_pre_1294_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_1305_) == 0 {
                            let mut v_str_1306_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1307_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1308_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1309_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1310_: u8 = 0;
                            v_str_1306_ = crate::leanh::lean_ctor_get(v_x_1292_, 1);
                            v_str_1307_ = crate::leanh::lean_ctor_get(v_pre_1293_, 1);
                            v_str_1308_ = crate::leanh::lean_ctor_get(v_pre_1294_, 1);
                            v___x_1309_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4;
                            v___x_1310_ = lean_string_dec_eq(v_str_1308_, v___x_1309_);
                            if v___x_1310_ == 0 {
                                return v___y_1290_;
                            } else {
                                let mut v___x_1311_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1312_: u8 = 0;
                                v___x_1311_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5;
                                v___x_1312_ = lean_string_dec_eq(v_str_1307_, v___x_1311_);
                                if v___x_1312_ == 0 {
                                    return v___y_1290_;
                                } else {
                                    let mut v___x_1313_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1314_: u8 = 0;
                                    v___x_1313_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6;
                                    v___x_1314_ = lean_string_dec_eq(v_str_1306_, v___x_1313_);
                                    if v___x_1314_ == 0 {
                                        return v___y_1290_;
                                    } else {
                                        return v_suppressElabErrors_1291_;
                                    }
                                }
                            }
                        } else {
                            return v___y_1290_;
                        }
                    }
                    _ => {
                        return v___y_1290_;
                    }
                }
            }
            0 => {
                let mut v_str_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1317_: u8 = 0;
                v_str_1315_ = crate::leanh::lean_ctor_get(v_x_1292_, 1);
                v___x_1316_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7;
                v___x_1317_ = lean_string_dec_eq(v_str_1315_, v___x_1316_);
                if v___x_1317_ == 0 {
                    return v___y_1290_;
                } else {
                    return v_suppressElabErrors_1291_;
                }
            }
            _ => {
                return v___y_1290_;
            }
        }
    } else {
        return v___y_1290_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___boxed(
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_11738__boxed_1321_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1322_: u8 = 0;
    let mut v_res_1323_: u8 = 0;
    let mut v_r_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_11738__boxed_1321_ = (crate::leanh::lean_unbox(v___y_1318_) as u8);
    v_suppressElabErrors_boxed_1322_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1319_) as u8);
    v_res_1323_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0(v___y_11738__boxed_1321_, v_suppressElabErrors_boxed_1322_, v_x_1320_);
    crate::leanh::lean_dec(v_x_1320_);
    v_r_1324_ = crate::leanh::lean_box((v_res_1323_) as usize);
    return v_r_1324_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(
    mut v_ref_1326_: *mut crate::leanh::LeanObject,
    mut v_msgData_1327_: *mut crate::leanh::LeanObject,
    mut v_severity_1328_: u8,
    mut v_isSilent_1329_: u8,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: u8 = 0;
    let mut v___y_1336_: u8 = 0;
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___y_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1371_: u8 = 0;
    let mut v___y_1372_: u8 = 0;
    let mut v___y_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: u8 = 0;
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut v___y_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1396_: u8 = 0;
    let mut v___y_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: u8 = 0;
    let mut v___y_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1400_: u8 = 0;
    let mut v___y_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1407_: u8 = 0;
    let mut v___y_1408_: u8 = 0;
    let mut v___y_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: u8 = 0;
    let mut v_ref_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v___y_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: u8 = 0;
    let mut v___y_1425_: u8 = 0;
    let mut v___y_1427_: u8 = 0;
    let mut v_fileName_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1417_ = 2;
                v___x_1442_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1328_, v___x_1417_);
                if v___x_1442_ == 0 {
                    v___y_1427_ = v___x_1442_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1327_);
                    v___x_1443_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1327_);
                    v___y_1427_ = v___x_1443_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1343_ = lean_st_ref_take(v___y_1342_);
                v_currNamespace_1344_ = crate::leanh::lean_ctor_get(v___y_1341_, 6);
                v_openDecls_1345_ = crate::leanh::lean_ctor_get(v___y_1341_, 7);
                v_env_1346_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                v_nextMacroScope_1347_ = crate::leanh::lean_ctor_get(v___x_1343_, 1);
                v_ngen_1348_ = crate::leanh::lean_ctor_get(v___x_1343_, 2);
                v_auxDeclNGen_1349_ = crate::leanh::lean_ctor_get(v___x_1343_, 3);
                v_traceState_1350_ = crate::leanh::lean_ctor_get(v___x_1343_, 4);
                v_cache_1351_ = crate::leanh::lean_ctor_get(v___x_1343_, 5);
                v_messages_1352_ = crate::leanh::lean_ctor_get(v___x_1343_, 6);
                v_infoState_1353_ = crate::leanh::lean_ctor_get(v___x_1343_, 7);
                v_snapshotTasks_1354_ = crate::leanh::lean_ctor_get(v___x_1343_, 8);
                v_isSharedCheck_1368_ = (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1368_ == 0 {
                    v___x_1356_ = v___x_1343_;
                    v_isShared_1357_ = v_isSharedCheck_1368_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1354_);
                    crate::leanh::lean_inc(v_infoState_1353_);
                    crate::leanh::lean_inc(v_messages_1352_);
                    crate::leanh::lean_inc(v_cache_1351_);
                    crate::leanh::lean_inc(v_traceState_1350_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1349_);
                    crate::leanh::lean_inc(v_ngen_1348_);
                    crate::leanh::lean_inc(v_nextMacroScope_1347_);
                    crate::leanh::lean_inc(v_env_1346_);
                    crate::leanh::lean_dec(v___x_1343_);
                    v___x_1356_ = crate::leanh::lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_1345_);
                crate::leanh::lean_inc(v_currNamespace_1344_);
                v___x_1358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1358_, 0, v_currNamespace_1344_);
                crate::leanh::lean_ctor_set(v___x_1358_, 1, v_openDecls_1345_);
                v___x_1359_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1358_);
                crate::leanh::lean_ctor_set(v___x_1359_, 1, v___y_1338_);
                crate::leanh::lean_inc_ref(v___y_1334_);
                crate::leanh::lean_inc_ref(v___y_1337_);
                v___x_1360_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1360_, 0, v___y_1337_);
                crate::leanh::lean_ctor_set(v___x_1360_, 1, v___y_1340_);
                crate::leanh::lean_ctor_set(v___x_1360_, 2, v___y_1339_);
                crate::leanh::lean_ctor_set(v___x_1360_, 3, v___y_1334_);
                crate::leanh::lean_ctor_set(v___x_1360_, 4, v___x_1359_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1335_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1336_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1329_,
                );
                v___x_1361_ = l_Lean_MessageLog_add(v___x_1360_, v_messages_1352_);
                if v_isShared_1357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1356_, 6, v___x_1361_);
                    v___x_1363_ = v___x_1356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_env_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_nextMacroScope_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_ngen_1348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_auxDeclNGen_1349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_traceState_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 5, v_cache_1351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 6, v___x_1361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 7, v_infoState_1353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 8, v_snapshotTasks_1354_);
                    v___x_1363_ = v_reuseFailAlloc_1367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1364_ = lean_st_ref_set(v___y_1342_, v___x_1363_);
                v___x_1365_ = crate::leanh::lean_box(0);
                v___x_1366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1365_);
                return v___x_1366_;
            }
            4 => {
                v___x_1378_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1327_,
                    );
                v___x_1379_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v___x_1378_, v___y_1330_, v___y_1331_);
                v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                v_isSharedCheck_1393_ = (!crate::leanh::lean_is_exclusive(v___x_1379_)) as u8;
                if v_isSharedCheck_1393_ == 0 {
                    v___x_1382_ = v___x_1379_;
                    v_isShared_1383_ = v_isSharedCheck_1393_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1380_);
                    crate::leanh::lean_dec(v___x_1379_);
                    v___x_1382_ = crate::leanh::lean_box(0);
                    v_isShared_1383_ = v_isSharedCheck_1393_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_1375_, 2);
                v___x_1384_ = l_Lean_FileMap_toPosition(v___y_1375_, v___y_1376_);
                crate::leanh::lean_dec(v___y_1376_);
                v___x_1385_ = l_Lean_FileMap_toPosition(v___y_1375_, v___y_1377_);
                crate::leanh::lean_dec(v___y_1377_);
                v___x_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1386_, 0, v___x_1385_);
                v___x_1387_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0;
                if v___y_1372_ == 0 {
                    crate::leanh::lean_del_object(v___x_1382_);
                    crate::leanh::lean_dec_ref(v___y_1370_);
                    v___y_1334_ = v___x_1387_;
                    v___y_1335_ = v___y_1371_;
                    v___y_1336_ = v___y_1374_;
                    v___y_1337_ = v___y_1373_;
                    v___y_1338_ = v_a_1380_;
                    v___y_1339_ = v___x_1386_;
                    v___y_1340_ = v___x_1384_;
                    v___y_1341_ = v___y_1330_;
                    v___y_1342_ = v___y_1331_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1380_);
                    v___x_1388_ = l_Lean_MessageData_hasTag(v___y_1370_, v_a_1380_);
                    if v___x_1388_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1386_, 1);
                        crate::leanh::lean_dec_ref(v___x_1384_);
                        crate::leanh::lean_dec(v_a_1380_);
                        v___x_1389_ = crate::leanh::lean_box(0);
                        if v_isShared_1383_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1382_, 0, v___x_1389_);
                            v___x_1391_ = v___x_1382_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1392_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
                            v___x_1391_ = v_reuseFailAlloc_1392_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1382_);
                        v___y_1334_ = v___x_1387_;
                        v___y_1335_ = v___y_1371_;
                        v___y_1336_ = v___y_1374_;
                        v___y_1337_ = v___y_1373_;
                        v___y_1338_ = v_a_1380_;
                        v___y_1339_ = v___x_1386_;
                        v___y_1340_ = v___x_1384_;
                        v___y_1341_ = v___y_1330_;
                        v___y_1342_ = v___y_1331_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1391_;
            }
            7 => {
                v___x_1403_ = l_Lean_Syntax_getTailPos_x3f(v___y_1401_, v___y_1396_);
                crate::leanh::lean_dec(v___y_1401_);
                if crate::leanh::lean_obj_tag(v___x_1403_) == 0 {
                    crate::leanh::lean_inc(v___y_1402_);
                    v___y_1370_ = v___y_1395_;
                    v___y_1371_ = v___y_1396_;
                    v___y_1372_ = v___y_1400_;
                    v___y_1373_ = v___y_1399_;
                    v___y_1374_ = v___y_1398_;
                    v___y_1375_ = v___y_1397_;
                    v___y_1376_ = v___y_1402_;
                    v___y_1377_ = v___y_1402_;
                    state = 4;
                    continue;
                } else {
                    v_val_1404_ = crate::leanh::lean_ctor_get(v___x_1403_, 0);
                    crate::leanh::lean_inc(v_val_1404_);
                    crate::leanh::lean_dec_ref_known(v___x_1403_, 1);
                    v___y_1370_ = v___y_1395_;
                    v___y_1371_ = v___y_1396_;
                    v___y_1372_ = v___y_1400_;
                    v___y_1373_ = v___y_1399_;
                    v___y_1374_ = v___y_1398_;
                    v___y_1375_ = v___y_1397_;
                    v___y_1376_ = v___y_1402_;
                    v___y_1377_ = v_val_1404_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_1413_ = l_Lean_replaceRef(v_ref_1326_, v___y_1411_);
                v___x_1414_ = l_Lean_Syntax_getPos_x3f(v_ref_1413_, v___y_1407_);
                if crate::leanh::lean_obj_tag(v___x_1414_) == 0 {
                    v___x_1415_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1395_ = v___y_1406_;
                    v___y_1396_ = v___y_1407_;
                    v___y_1397_ = v___y_1410_;
                    v___y_1398_ = v___y_1412_;
                    v___y_1399_ = v___y_1409_;
                    v___y_1400_ = v___y_1408_;
                    v___y_1401_ = v_ref_1413_;
                    v___y_1402_ = v___x_1415_;
                    state = 7;
                    continue;
                } else {
                    v_val_1416_ = crate::leanh::lean_ctor_get(v___x_1414_, 0);
                    crate::leanh::lean_inc(v_val_1416_);
                    crate::leanh::lean_dec_ref_known(v___x_1414_, 1);
                    v___y_1395_ = v___y_1406_;
                    v___y_1396_ = v___y_1407_;
                    v___y_1397_ = v___y_1410_;
                    v___y_1398_ = v___y_1412_;
                    v___y_1399_ = v___y_1409_;
                    v___y_1400_ = v___y_1408_;
                    v___y_1401_ = v_ref_1413_;
                    v___y_1402_ = v_val_1416_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_1425_ == 0 {
                    v___y_1406_ = v___y_1423_;
                    v___y_1407_ = v___y_1424_;
                    v___y_1408_ = v___y_1421_;
                    v___y_1409_ = v___y_1420_;
                    v___y_1410_ = v___y_1419_;
                    v___y_1411_ = v___y_1422_;
                    v___y_1412_ = v_severity_1328_;
                    state = 8;
                    continue;
                } else {
                    v___y_1406_ = v___y_1423_;
                    v___y_1407_ = v___y_1424_;
                    v___y_1408_ = v___y_1421_;
                    v___y_1409_ = v___y_1420_;
                    v___y_1410_ = v___y_1419_;
                    v___y_1411_ = v___y_1422_;
                    v___y_1412_ = v___x_1417_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_1427_ == 0 {
                    v_fileName_1428_ = crate::leanh::lean_ctor_get(v___y_1330_, 0);
                    v_fileMap_1429_ = crate::leanh::lean_ctor_get(v___y_1330_, 1);
                    v_options_1430_ = crate::leanh::lean_ctor_get(v___y_1330_, 2);
                    v_ref_1431_ = crate::leanh::lean_ctor_get(v___y_1330_, 5);
                    v_suppressElabErrors_1432_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1330_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_1433_ = crate::leanh::lean_box((v___y_1427_) as usize);
                    v___x_1434_ = crate::leanh::lean_box((v_suppressElabErrors_1432_) as usize);
                    v___f_1435_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1435_, 0, v___x_1433_);
                    crate::leanh::lean_closure_set(v___f_1435_, 1, v___x_1434_);
                    v___x_1436_ = 1;
                    v___x_1437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1328_, v___x_1436_);
                    if v___x_1437_ == 0 {
                        v___y_1419_ = v_fileMap_1429_;
                        v___y_1420_ = v_fileName_1428_;
                        v___y_1421_ = v_suppressElabErrors_1432_;
                        v___y_1422_ = v_ref_1431_;
                        v___y_1423_ = v___f_1435_;
                        v___y_1424_ = v___y_1427_;
                        v___y_1425_ = v___x_1437_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1438_ = l_Lean_warningAsError;
                        v___x_1439_ = l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(v_options_1430_, v___x_1438_);
                        v___y_1419_ = v_fileMap_1429_;
                        v___y_1420_ = v_fileName_1428_;
                        v___y_1421_ = v_suppressElabErrors_1432_;
                        v___y_1422_ = v_ref_1431_;
                        v___y_1423_ = v___f_1435_;
                        v___y_1424_ = v___y_1427_;
                        v___y_1425_ = v___x_1439_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1327_);
                    v___x_1440_ = crate::leanh::lean_box(0);
                    v___x_1441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1441_, 0, v___x_1440_);
                    return v___x_1441_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___boxed(
    mut v_ref_1444_: *mut crate::leanh::LeanObject,
    mut v_msgData_1445_: *mut crate::leanh::LeanObject,
    mut v_severity_1446_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1451_: u8 = 0;
    let mut v_isSilent_boxed_1452_: u8 = 0;
    let mut v_res_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1451_ = (crate::leanh::lean_unbox(v_severity_1446_) as u8);
    v_isSilent_boxed_1452_ = (crate::leanh::lean_unbox(v_isSilent_1447_) as u8);
    v_res_1453_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1444_, v_msgData_1445_, v_severity_boxed_1451_, v_isSilent_boxed_1452_, v___y_1448_, v___y_1449_);
    crate::leanh::lean_dec(v___y_1449_);
    crate::leanh::lean_dec_ref(v___y_1448_);
    crate::leanh::lean_dec(v_ref_1444_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(
    mut v_msgData_1454_: *mut crate::leanh::LeanObject,
    mut v_severity_1455_: u8,
    mut v_isSilent_1456_: u8,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1460_ = crate::leanh::lean_ctor_get(v___y_1457_, 5);
    v___x_1461_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1460_, v_msgData_1454_, v_severity_1455_, v_isSilent_1456_, v___y_1457_, v___y_1458_);
    return v___x_1461_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12___boxed(
    mut v_msgData_1462_: *mut crate::leanh::LeanObject,
    mut v_severity_1463_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1468_: u8 = 0;
    let mut v_isSilent_boxed_1469_: u8 = 0;
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1468_ = (crate::leanh::lean_unbox(v_severity_1463_) as u8);
    v_isSilent_boxed_1469_ = (crate::leanh::lean_unbox(v_isSilent_1464_) as u8);
    v_res_1470_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(v_msgData_1462_, v_severity_boxed_1468_, v_isSilent_boxed_1469_, v___y_1465_, v___y_1466_);
    crate::leanh::lean_dec(v___y_1466_);
    crate::leanh::lean_dec_ref(v___y_1465_);
    return v_res_1470_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(
    mut v_msgData_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1475_ = 1;
    v___x_1476_ = 0;
    v___x_1477_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(v_msgData_1471_, v___x_1475_, v___x_1476_, v___y_1472_, v___y_1473_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6___boxed(
    mut v_msgData_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(v_msgData_1478_, v___y_1479_, v___y_1480_);
    crate::leanh::lean_dec(v___y_1480_);
    crate::leanh::lean_dec_ref(v___y_1479_);
    return v_res_1482_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1484_: u8,
    mut v___x_1485_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_unused_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1488_ = lean_st_ref_take(v___y_1483_);
                v_env_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                v_nextMacroScope_1490_ = crate::leanh::lean_ctor_get(v___x_1488_, 1);
                v_ngen_1491_ = crate::leanh::lean_ctor_get(v___x_1488_, 2);
                v_auxDeclNGen_1492_ = crate::leanh::lean_ctor_get(v___x_1488_, 3);
                v_traceState_1493_ = crate::leanh::lean_ctor_get(v___x_1488_, 4);
                v_messages_1494_ = crate::leanh::lean_ctor_get(v___x_1488_, 6);
                v_infoState_1495_ = crate::leanh::lean_ctor_get(v___x_1488_, 7);
                v_snapshotTasks_1496_ = crate::leanh::lean_ctor_get(v___x_1488_, 8);
                v_isSharedCheck_1507_ = (!crate::leanh::lean_is_exclusive(v___x_1488_)) as u8;
                if v_isSharedCheck_1507_ == 0 {
                    v_unused_1508_ = crate::leanh::lean_ctor_get(v___x_1488_, 5);
                    crate::leanh::lean_dec(v_unused_1508_);
                    v___x_1498_ = v___x_1488_;
                    v_isShared_1499_ = v_isSharedCheck_1507_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1496_);
                    crate::leanh::lean_inc(v_infoState_1495_);
                    crate::leanh::lean_inc(v_messages_1494_);
                    crate::leanh::lean_inc(v_traceState_1493_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1492_);
                    crate::leanh::lean_inc(v_ngen_1491_);
                    crate::leanh::lean_inc(v_nextMacroScope_1490_);
                    crate::leanh::lean_inc(v_env_1489_);
                    crate::leanh::lean_dec(v___x_1488_);
                    v___x_1498_ = crate::leanh::lean_box(0);
                    v_isShared_1499_ = v_isSharedCheck_1507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1500_ = l_Lean_Environment_setExporting(v_env_1489_, v_isExporting_1484_);
                if v_isShared_1499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1498_, 5, v___x_1485_);
                    crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1500_);
                    v___x_1502_ = v___x_1498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_nextMacroScope_1490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_ngen_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_auxDeclNGen_1492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_traceState_1493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 5, v___x_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_messages_1494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_infoState_1495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_snapshotTasks_1496_);
                    v___x_1502_ = v_reuseFailAlloc_1506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1503_ = lean_st_ref_set(v___y_1483_, v___x_1502_);
                v___x_1504_ = crate::leanh::lean_box(0);
                v___x_1505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                return v___x_1505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1510_: *mut crate::leanh::LeanObject,
    mut v___x_1511_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_1514_: u8 = 0;
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1514_ = (crate::leanh::lean_unbox(v_isExporting_1510_) as u8);
    v_res_1515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1509_, v_isExporting_boxed_1514_, v___x_1511_, v_a_x3f_1512_);
    crate::leanh::lean_dec(v_a_x3f_1512_);
    crate::leanh::lean_dec(v___y_1509_);
    return v_res_1515_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1516_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0);
    v___x_1518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
    v___x_1520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
    crate::leanh::lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_1521_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1522_: u8,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1528_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_unused_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1526_ = lean_st_ref_get(v___y_1524_);
                v_env_1527_ = crate::leanh::lean_ctor_get(v___x_1526_, 0);
                crate::leanh::lean_inc_ref(v_env_1527_);
                crate::leanh::lean_dec(v___x_1526_);
                v_isExporting_1528_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1527_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_1527_);
                v___x_1529_ = lean_st_ref_take(v___y_1524_);
                v_env_1530_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                v_nextMacroScope_1531_ = crate::leanh::lean_ctor_get(v___x_1529_, 1);
                v_ngen_1532_ = crate::leanh::lean_ctor_get(v___x_1529_, 2);
                v_auxDeclNGen_1533_ = crate::leanh::lean_ctor_get(v___x_1529_, 3);
                v_traceState_1534_ = crate::leanh::lean_ctor_get(v___x_1529_, 4);
                v_messages_1535_ = crate::leanh::lean_ctor_get(v___x_1529_, 6);
                v_infoState_1536_ = crate::leanh::lean_ctor_get(v___x_1529_, 7);
                v_snapshotTasks_1537_ = crate::leanh::lean_ctor_get(v___x_1529_, 8);
                v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v___x_1529_)) as u8;
                if v_isSharedCheck_1576_ == 0 {
                    v_unused_1577_ = crate::leanh::lean_ctor_get(v___x_1529_, 5);
                    crate::leanh::lean_dec(v_unused_1577_);
                    v___x_1539_ = v___x_1529_;
                    v_isShared_1540_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1537_);
                    crate::leanh::lean_inc(v_infoState_1536_);
                    crate::leanh::lean_inc(v_messages_1535_);
                    crate::leanh::lean_inc(v_traceState_1534_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1533_);
                    crate::leanh::lean_inc(v_ngen_1532_);
                    crate::leanh::lean_inc(v_nextMacroScope_1531_);
                    crate::leanh::lean_inc(v_env_1530_);
                    crate::leanh::lean_dec(v___x_1529_);
                    v___x_1539_ = crate::leanh::lean_box(0);
                    v_isShared_1540_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1541_ = l_Lean_Environment_setExporting(v_env_1530_, v_isExporting_1522_);
                v___x_1542_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2);
                if v_isShared_1540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1539_, 5, v___x_1542_);
                    crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1541_);
                    v___x_1544_ = v___x_1539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_messages_1535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_infoState_1536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_snapshotTasks_1537_);
                    v___x_1544_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1545_ = lean_st_ref_set(v___y_1524_, v___x_1544_);
                crate::leanh::lean_inc(v___y_1524_);
                crate::leanh::lean_inc_ref(v___y_1523_);
                v_r_1546_ = crate::leanh::lean_apply_3(
                    v_x_1521_,
                    v___y_1523_,
                    v___y_1524_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1546_) == 0 {
                    v_a_1547_ = crate::leanh::lean_ctor_get(v_r_1546_, 0);
                    v_isSharedCheck_1563_ = (!crate::leanh::lean_is_exclusive(v_r_1546_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v___x_1549_ = v_r_1546_;
                        v_isShared_1550_ = v_isSharedCheck_1563_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1547_);
                        crate::leanh::lean_dec(v_r_1546_);
                        v___x_1549_ = crate::leanh::lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1563_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1564_ = crate::leanh::lean_ctor_get(v_r_1546_, 0);
                    crate::leanh::lean_inc(v_a_1564_);
                    crate::leanh::lean_dec_ref_known(v_r_1546_, 1);
                    v___x_1565_ = crate::leanh::lean_box(0);
                    v___x_1566_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1524_, v_isExporting_1528_, v___x_1542_, v___x_1565_);
                    v_isSharedCheck_1573_ = (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v_unused_1574_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                        crate::leanh::lean_dec(v_unused_1574_);
                        v___x_1568_ = v___x_1566_;
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1566_);
                        v___x_1568_ = crate::leanh::lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_1547_);
                if v_isShared_1550_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1549_, 1);
                    v___x_1552_ = v___x_1549_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1547_);
                    v___x_1552_ = v_reuseFailAlloc_1562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1524_, v_isExporting_1528_, v___x_1542_, v___x_1552_);
                crate::leanh::lean_dec_ref(v___x_1552_);
                v_isSharedCheck_1560_ = (!crate::leanh::lean_is_exclusive(v___x_1553_)) as u8;
                if v_isSharedCheck_1560_ == 0 {
                    v_unused_1561_ = crate::leanh::lean_ctor_get(v___x_1553_, 0);
                    crate::leanh::lean_dec(v_unused_1561_);
                    v___x_1555_ = v___x_1553_;
                    v_isShared_1556_ = v_isSharedCheck_1560_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1553_);
                    v___x_1555_ = crate::leanh::lean_box(0);
                    v_isShared_1556_ = v_isSharedCheck_1560_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1555_, 0, v_a_1547_);
                    v___x_1558_ = v___x_1555_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1547_);
                    v___x_1558_ = v_reuseFailAlloc_1559_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1558_;
            }
            7 => {
                if v_isShared_1569_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1568_, 1);
                    crate::leanh::lean_ctor_set(v___x_1568_, 0, v_a_1564_);
                    v___x_1571_ = v___x_1568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1564_);
                    v___x_1571_ = v_reuseFailAlloc_1572_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_x_1578_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1583_ = (crate::leanh::lean_unbox(v_isExporting_1579_) as u8);
    v_res_1584_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_1578_, v_isExporting_boxed_1583_, v___y_1580_, v___y_1581_);
    crate::leanh::lean_dec(v___y_1581_);
    crate::leanh::lean_dec_ref(v___y_1580_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_1585_: *mut crate::leanh::LeanObject,
    mut v_when_1586_: u8,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_1586_ == 0 {
        let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_1588_);
        crate::leanh::lean_inc_ref(v___y_1587_);
        v___x_1590_ = crate::leanh::lean_apply_3(
            v_x_1585_,
            v___y_1587_,
            v___y_1588_,
            crate::leanh::lean_box(0),
        );
        return v___x_1590_;
    } else {
        let mut v___x_1591_: u8 = 0;
        let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1591_ = 0;
        v___x_1592_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_1585_, v___x_1591_, v___y_1587_, v___y_1588_);
        return v___x_1592_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_1593_: *mut crate::leanh::LeanObject,
    mut v_when_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_1598_ = (crate::leanh::lean_unbox(v_when_1594_) as u8);
    v_res_1599_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v_x_1593_, v_when_boxed_1598_, v___y_1595_, v___y_1596_);
    crate::leanh::lean_dec(v___y_1596_);
    crate::leanh::lean_dec_ref(v___y_1595_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(
    mut v_ref_1600_: *mut crate::leanh::LeanObject,
    mut v_msgData_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = 1;
    v___x_1606_ = 0;
    v___x_1607_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1600_, v_msgData_1601_, v___x_1605_, v___x_1606_, v___y_1602_, v___y_1603_);
    return v___x_1607_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4___boxed(
    mut v_ref_1608_: *mut crate::leanh::LeanObject,
    mut v_msgData_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(v_ref_1608_, v_msgData_1609_, v___y_1610_, v___y_1611_);
    crate::leanh::lean_dec(v___y_1611_);
    crate::leanh::lean_dec_ref(v___y_1610_);
    crate::leanh::lean_dec(v_ref_1608_);
    return v_res_1613_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1618_ = crate::leanh::lean_ctor_get(v___y_1615_, 5);
                v___x_1619_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v_msg_1614_, v___y_1615_, v___y_1616_);
                v_a_1620_ = crate::leanh::lean_ctor_get(v___x_1619_, 0);
                v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___x_1619_)) as u8;
                if v_isSharedCheck_1628_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    v_isShared_1623_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1620_);
                    crate::leanh::lean_dec(v___x_1619_);
                    v___x_1622_ = crate::leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1618_);
                v___x_1624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1624_, 0, v_ref_1618_);
                crate::leanh::lean_ctor_set(v___x_1624_, 1, v_a_1620_);
                if v_isShared_1623_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1622_, 1);
                    crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1624_);
                    v___x_1626_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_1629_, v___y_1630_, v___y_1631_);
    crate::leanh::lean_dec(v___y_1631_);
    crate::leanh::lean_dec_ref(v___y_1630_);
    return v_res_1633_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0;
    v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2;
    v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
    return v___x_1639_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4;
    v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(
    mut v_name_1646_: *mut crate::leanh::LeanObject,
    mut v_kind_1647_: u8,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1);
                v___x_1652_ = l_Lean_MessageData_ofName(v_name_1646_);
                v___x_1653_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1651_);
                crate::leanh::lean_ctor_set(v___x_1653_, 1, v___x_1652_);
                v___x_1654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3);
                v___x_1655_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1653_);
                crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
                match v_kind_1647_ {
                    0 => {
                        v___x_1664_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6;
                        v___y_1657_ = v___x_1664_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1665_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7;
                        v___y_1657_ = v___x_1665_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1666_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8;
                        v___y_1657_ = v___x_1666_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1657_);
                v___x_1658_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1658_, 0, v___y_1657_);
                v___x_1659_ = l_Lean_MessageData_ofFormat(v___x_1658_);
                v___x_1660_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1655_);
                crate::leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                v___x_1661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5);
                v___x_1662_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1660_);
                crate::leanh::lean_ctor_set(v___x_1662_, 1, v___x_1661_);
                v___x_1663_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_1662_, v___y_1648_, v___y_1649_);
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___boxed(
    mut v_name_1667_: *mut crate::leanh::LeanObject,
    mut v_kind_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1672_: u8 = 0;
    let mut v_res_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1672_ = (crate::leanh::lean_unbox(v_kind_1668_) as u8);
    v_res_1673_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v_name_1667_, v_kind_boxed_1672_, v___y_1669_, v___y_1670_);
    crate::leanh::lean_dec(v___y_1670_);
    crate::leanh::lean_dec_ref(v___y_1669_);
    return v_res_1673_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(
    mut v_ref_1674_: *mut crate::leanh::LeanObject,
    mut v_msg_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1691_: u8 = 0;
    let mut v_cancelTk_x3f_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1693_: u8 = 0;
    let mut v_inheritedTraceOptions_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1679_ = crate::leanh::lean_ctor_get(v___y_1676_, 0);
    v_fileMap_1680_ = crate::leanh::lean_ctor_get(v___y_1676_, 1);
    v_options_1681_ = crate::leanh::lean_ctor_get(v___y_1676_, 2);
    v_currRecDepth_1682_ = crate::leanh::lean_ctor_get(v___y_1676_, 3);
    v_maxRecDepth_1683_ = crate::leanh::lean_ctor_get(v___y_1676_, 4);
    v_ref_1684_ = crate::leanh::lean_ctor_get(v___y_1676_, 5);
    v_currNamespace_1685_ = crate::leanh::lean_ctor_get(v___y_1676_, 6);
    v_openDecls_1686_ = crate::leanh::lean_ctor_get(v___y_1676_, 7);
    v_initHeartbeats_1687_ = crate::leanh::lean_ctor_get(v___y_1676_, 8);
    v_maxHeartbeats_1688_ = crate::leanh::lean_ctor_get(v___y_1676_, 9);
    v_quotContext_1689_ = crate::leanh::lean_ctor_get(v___y_1676_, 10);
    v_currMacroScope_1690_ = crate::leanh::lean_ctor_get(v___y_1676_, 11);
    v_diag_1691_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1676_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1692_ = crate::leanh::lean_ctor_get(v___y_1676_, 12);
    v_suppressElabErrors_1693_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1676_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1694_ = crate::leanh::lean_ctor_get(v___y_1676_, 13);
    v_ref_1695_ = l_Lean_replaceRef(v_ref_1674_, v_ref_1684_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1694_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1692_);
    crate::leanh::lean_inc(v_currMacroScope_1690_);
    crate::leanh::lean_inc(v_quotContext_1689_);
    crate::leanh::lean_inc(v_maxHeartbeats_1688_);
    crate::leanh::lean_inc(v_initHeartbeats_1687_);
    crate::leanh::lean_inc(v_openDecls_1686_);
    crate::leanh::lean_inc(v_currNamespace_1685_);
    crate::leanh::lean_inc(v_maxRecDepth_1683_);
    crate::leanh::lean_inc(v_currRecDepth_1682_);
    crate::leanh::lean_inc_ref(v_options_1681_);
    crate::leanh::lean_inc_ref(v_fileMap_1680_);
    crate::leanh::lean_inc_ref(v_fileName_1679_);
    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1696_, 0, v_fileName_1679_);
    crate::leanh::lean_ctor_set(v___x_1696_, 1, v_fileMap_1680_);
    crate::leanh::lean_ctor_set(v___x_1696_, 2, v_options_1681_);
    crate::leanh::lean_ctor_set(v___x_1696_, 3, v_currRecDepth_1682_);
    crate::leanh::lean_ctor_set(v___x_1696_, 4, v_maxRecDepth_1683_);
    crate::leanh::lean_ctor_set(v___x_1696_, 5, v_ref_1695_);
    crate::leanh::lean_ctor_set(v___x_1696_, 6, v_currNamespace_1685_);
    crate::leanh::lean_ctor_set(v___x_1696_, 7, v_openDecls_1686_);
    crate::leanh::lean_ctor_set(v___x_1696_, 8, v_initHeartbeats_1687_);
    crate::leanh::lean_ctor_set(v___x_1696_, 9, v_maxHeartbeats_1688_);
    crate::leanh::lean_ctor_set(v___x_1696_, 10, v_quotContext_1689_);
    crate::leanh::lean_ctor_set(v___x_1696_, 11, v_currMacroScope_1690_);
    crate::leanh::lean_ctor_set(v___x_1696_, 12, v_cancelTk_x3f_1692_);
    crate::leanh::lean_ctor_set(v___x_1696_, 13, v_inheritedTraceOptions_1694_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1696_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1691_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1696_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1693_,
    );
    v___x_1697_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_1675_, v___x_1696_, v___y_1677_);
    crate::leanh::lean_dec_ref_known(v___x_1696_, 14);
    return v___x_1697_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg___boxed(
    mut v_ref_1698_: *mut crate::leanh::LeanObject,
    mut v_msg_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_1698_, v_msg_1699_, v___y_1700_, v___y_1701_);
    crate::leanh::lean_dec(v___y_1701_);
    crate::leanh::lean_dec_ref(v___y_1700_);
    crate::leanh::lean_dec(v_ref_1698_);
    return v_res_1703_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0;
    v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2;
    v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4;
    v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(
    mut v_msg_1725_: *mut crate::leanh::LeanObject,
    mut v_declHint_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v_isExporting_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1729_ = lean_st_ref_get(v___y_1727_);
                v_env_1730_ = crate::leanh::lean_ctor_get(v___x_1729_, 0);
                crate::leanh::lean_inc_ref(v_env_1730_);
                crate::leanh::lean_dec(v___x_1729_);
                v___x_1731_ = l_Lean_Name_isAnonymous(v_declHint_1726_);
                if v___x_1731_ == 0 {
                    v_isExporting_1732_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1730_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1732_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1730_);
                        crate::leanh::lean_dec(v_declHint_1726_);
                        v___x_1733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1733_, 0, v_msg_1725_);
                        return v___x_1733_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1730_);
                        v___x_1734_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1731_);
                        crate::leanh::lean_inc(v_declHint_1726_);
                        crate::leanh::lean_inc_ref(v___x_1734_);
                        v___x_1735_ = l_Lean_Environment_contains(
                            v___x_1734_,
                            v_declHint_1726_,
                            v_isExporting_1732_,
                        );
                        if v___x_1735_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1734_);
                            crate::leanh::lean_dec_ref(v_env_1730_);
                            crate::leanh::lean_dec(v_declHint_1726_);
                            v___x_1736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1736_, 0, v_msg_1725_);
                            return v___x_1736_;
                        } else {
                            v___x_1737_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2);
                            v___x_1738_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5);
                            v___x_1739_ = l_Lean_Options_empty;
                            v___x_1740_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1734_);
                            crate::leanh::lean_ctor_set(v___x_1740_, 1, v___x_1737_);
                            crate::leanh::lean_ctor_set(v___x_1740_, 2, v___x_1738_);
                            crate::leanh::lean_ctor_set(v___x_1740_, 3, v___x_1739_);
                            crate::leanh::lean_inc(v_declHint_1726_);
                            v___x_1741_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1726_, v___x_1731_);
                            v_c_1742_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1742_, 0, v___x_1740_);
                            crate::leanh::lean_ctor_set(v_c_1742_, 1, v___x_1741_);
                            v___x_1743_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1730_,
                                v_declHint_1726_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1743_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1730_);
                                crate::leanh::lean_dec(v_declHint_1726_);
                                v___x_1744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1);
                                v___x_1745_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
                                crate::leanh::lean_ctor_set(v___x_1745_, 1, v_c_1742_);
                                v___x_1746_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3);
                                v___x_1747_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                                crate::leanh::lean_ctor_set(v___x_1747_, 1, v___x_1746_);
                                v___x_1748_ = l_Lean_MessageData_note(v___x_1747_);
                                v___x_1749_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1749_, 0, v_msg_1725_);
                                crate::leanh::lean_ctor_set(v___x_1749_, 1, v___x_1748_);
                                v___x_1750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1750_, 0, v___x_1749_);
                                return v___x_1750_;
                            } else {
                                v_val_1751_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                                v_isSharedCheck_1786_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1743_)) as u8;
                                if v_isSharedCheck_1786_ == 0 {
                                    v___x_1753_ = v___x_1743_;
                                    v_isShared_1754_ = v_isSharedCheck_1786_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1751_);
                                    crate::leanh::lean_dec(v___x_1743_);
                                    v___x_1753_ = crate::leanh::lean_box(0);
                                    v_isShared_1754_ = v_isSharedCheck_1786_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1730_);
                    crate::leanh::lean_dec(v_declHint_1726_);
                    v___x_1787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1787_, 0, v_msg_1725_);
                    return v___x_1787_;
                }
            }
            1 => {
                v___x_1755_ = crate::leanh::lean_box(0);
                v___x_1756_ = l_Lean_Environment_header(v_env_1730_);
                crate::leanh::lean_dec_ref(v_env_1730_);
                v___x_1757_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1756_);
                v_mod_1758_ = lean_array_get(v___x_1755_, v___x_1757_, v_val_1751_);
                crate::leanh::lean_dec(v_val_1751_);
                crate::leanh::lean_dec_ref(v___x_1757_);
                v___x_1759_ = l_Lean_isPrivateName(v_declHint_1726_);
                crate::leanh::lean_dec(v_declHint_1726_);
                if v___x_1759_ == 0 {
                    v___x_1760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5);
                    v___x_1761_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
                    crate::leanh::lean_ctor_set(v___x_1761_, 1, v_c_1742_);
                    v___x_1762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_1763_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1761_);
                    crate::leanh::lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                    v___x_1764_ = l_Lean_MessageData_ofName(v_mod_1758_);
                    v___x_1765_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                    crate::leanh::lean_ctor_set(v___x_1765_, 1, v___x_1764_);
                    v___x_1766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9);
                    v___x_1767_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1765_);
                    crate::leanh::lean_ctor_set(v___x_1767_, 1, v___x_1766_);
                    v___x_1768_ = l_Lean_MessageData_note(v___x_1767_);
                    v___x_1769_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1769_, 0, v_msg_1725_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 1, v___x_1768_);
                    if v_isShared_1754_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1753_, 0);
                        crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1769_);
                        v___x_1771_ = v___x_1753_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                        v___x_1771_ = v_reuseFailAlloc_1772_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1773_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1);
                    v___x_1774_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1774_, 0, v___x_1773_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 1, v_c_1742_);
                    v___x_1775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_1776_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1774_);
                    crate::leanh::lean_ctor_set(v___x_1776_, 1, v___x_1775_);
                    v___x_1777_ = l_Lean_MessageData_ofName(v_mod_1758_);
                    v___x_1778_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1776_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v___x_1777_);
                    v___x_1779_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_1780_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1778_);
                    crate::leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
                    v___x_1781_ = l_Lean_MessageData_note(v___x_1780_);
                    v___x_1782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1782_, 0, v_msg_1725_);
                    crate::leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
                    if v_isShared_1754_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1753_, 0);
                        crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1782_);
                        v___x_1784_ = v___x_1753_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
                        v___x_1784_ = v_reuseFailAlloc_1785_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1771_;
            }
            3 => {
                return v___x_1784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___boxed(
    mut v_msg_1788_: *mut crate::leanh::LeanObject,
    mut v_declHint_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_1788_, v_declHint_1789_, v___y_1790_);
    crate::leanh::lean_dec(v___y_1790_);
    return v_res_1792_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(
    mut v_msg_1793_: *mut crate::leanh::LeanObject,
    mut v_declHint_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1798_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_1793_, v_declHint_1794_, v___y_1796_);
                v_a_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                v_isSharedCheck_1808_ = (!crate::leanh::lean_is_exclusive(v___x_1798_)) as u8;
                if v_isSharedCheck_1808_ == 0 {
                    v___x_1801_ = v___x_1798_;
                    v_isShared_1802_ = v_isSharedCheck_1808_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1799_);
                    crate::leanh::lean_dec(v___x_1798_);
                    v___x_1801_ = crate::leanh::lean_box(0);
                    v_isShared_1802_ = v_isSharedCheck_1808_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1803_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1804_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                crate::leanh::lean_ctor_set(v___x_1804_, 1, v_a_1799_);
                if v_isShared_1802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1804_);
                    v___x_1806_ = v___x_1801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
                    v___x_1806_ = v_reuseFailAlloc_1807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17___boxed(
    mut v_msg_1809_: *mut crate::leanh::LeanObject,
    mut v_declHint_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(v_msg_1809_, v_declHint_1810_, v___y_1811_, v___y_1812_);
    crate::leanh::lean_dec(v___y_1812_);
    crate::leanh::lean_dec_ref(v___y_1811_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(
    mut v_ref_1815_: *mut crate::leanh::LeanObject,
    mut v_msg_1816_: *mut crate::leanh::LeanObject,
    mut v_declHint_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(v_msg_1816_, v_declHint_1817_, v___y_1818_, v___y_1819_);
    v_a_1822_ = crate::leanh::lean_ctor_get(v___x_1821_, 0);
    crate::leanh::lean_inc(v_a_1822_);
    crate::leanh::lean_dec_ref(v___x_1821_);
    v___x_1823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_1815_, v_a_1822_, v___y_1818_, v___y_1819_);
    return v___x_1823_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg___boxed(
    mut v_ref_1824_: *mut crate::leanh::LeanObject,
    mut v_msg_1825_: *mut crate::leanh::LeanObject,
    mut v_declHint_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_1824_, v_msg_1825_, v_declHint_1826_, v___y_1827_, v___y_1828_);
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    crate::leanh::lean_dec(v_ref_1824_);
    return v_res_1830_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0;
    v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(
    mut v_ref_1834_: *mut crate::leanh::LeanObject,
    mut v_constName_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1);
    v___x_1840_ = 0;
    crate::leanh::lean_inc(v_constName_1835_);
    v___x_1841_ = l_Lean_MessageData_ofConstName(v_constName_1835_, v___x_1840_);
    v___x_1842_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1842_, 0, v___x_1839_);
    crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1841_);
    v___x_1843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5);
    v___x_1844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1844_, 0, v___x_1842_);
    crate::leanh::lean_ctor_set(v___x_1844_, 1, v___x_1843_);
    v___x_1845_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_1834_, v___x_1844_, v_constName_1835_, v___y_1836_, v___y_1837_);
    return v___x_1845_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___boxed(
    mut v_ref_1846_: *mut crate::leanh::LeanObject,
    mut v_constName_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_1846_, v_constName_1847_, v___y_1848_, v___y_1849_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    crate::leanh::lean_dec(v_ref_1846_);
    return v_res_1851_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(
    mut v_constName_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1856_ = crate::leanh::lean_ctor_get(v___y_1853_, 5);
    v___x_1857_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_1856_, v_constName_1852_, v___y_1853_, v___y_1854_);
    return v___x_1857_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg___boxed(
    mut v_constName_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_1858_, v___y_1859_, v___y_1860_);
    crate::leanh::lean_dec(v___y_1860_);
    crate::leanh::lean_dec_ref(v___y_1859_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(
    mut v_constName_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1867_ = lean_st_ref_get(v___y_1865_);
                v_env_1868_ = crate::leanh::lean_ctor_get(v___x_1867_, 0);
                crate::leanh::lean_inc_ref(v_env_1868_);
                crate::leanh::lean_dec(v___x_1867_);
                v___x_1869_ = 0;
                crate::leanh::lean_inc(v_constName_1863_);
                v___x_1870_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_1868_,
                    v_constName_1863_,
                    v___x_1869_,
                );
                if crate::leanh::lean_obj_tag(v___x_1870_) == 0 {
                    v___x_1871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_1863_, v___y_1864_, v___y_1865_);
                    return v___x_1871_;
                } else {
                    crate::leanh::lean_dec(v_constName_1863_);
                    v_val_1872_ = crate::leanh::lean_ctor_get(v___x_1870_, 0);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v___x_1870_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1874_ = v___x_1870_;
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1872_);
                        crate::leanh::lean_dec(v___x_1870_);
                        v___x_1874_ = crate::leanh::lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1875_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1874_, 0);
                    v___x_1877_ = v___x_1874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_val_1872_);
                    v___x_1877_ = v_reuseFailAlloc_1878_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6___boxed(
    mut v_constName_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(v_constName_1880_, v___y_1881_, v___y_1882_);
    crate::leanh::lean_dec(v___y_1882_);
    crate::leanh::lean_dec_ref(v___y_1881_);
    return v_res_1884_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__7(
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1885_) == 0 {
                    v___x_1887_ = l_List_reverse___redArg(v_a_1886_);
                    return v___x_1887_;
                } else {
                    v_head_1888_ = crate::leanh::lean_ctor_get(v_a_1885_, 0);
                    v_tail_1889_ = crate::leanh::lean_ctor_get(v_a_1885_, 1);
                    v_isSharedCheck_1898_ = (!crate::leanh::lean_is_exclusive(v_a_1885_)) as u8;
                    if v_isSharedCheck_1898_ == 0 {
                        v___x_1891_ = v_a_1885_;
                        v_isShared_1892_ = v_isSharedCheck_1898_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1889_);
                        crate::leanh::lean_inc(v_head_1888_);
                        crate::leanh::lean_dec(v_a_1885_);
                        v___x_1891_ = crate::leanh::lean_box(0);
                        v_isShared_1892_ = v_isSharedCheck_1898_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1893_ = l_Lean_mkLevelParam(v_head_1888_);
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 1, v_a_1886_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1893_);
                    v___x_1895_ = v___x_1891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_a_1886_);
                    v___x_1895_ = v_reuseFailAlloc_1897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1885_ = v_tail_1889_;
                v_a_1886_ = v___x_1895_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(
    mut v_constName_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v_levelParams_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_a_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_1899_);
                v___x_1903_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(v_constName_1899_, v___y_1900_, v___y_1901_);
                if crate::leanh::lean_obj_tag(v___x_1903_) == 0 {
                    v_a_1904_ = crate::leanh::lean_ctor_get(v___x_1903_, 0);
                    v_isSharedCheck_1915_ = (!crate::leanh::lean_is_exclusive(v___x_1903_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1906_ = v___x_1903_;
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1904_);
                        crate::leanh::lean_dec(v___x_1903_);
                        v___x_1906_ = crate::leanh::lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_1899_);
                    v_a_1916_ = crate::leanh::lean_ctor_get(v___x_1903_, 0);
                    v_isSharedCheck_1923_ = (!crate::leanh::lean_is_exclusive(v___x_1903_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1903_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1916_);
                        crate::leanh::lean_dec(v___x_1903_);
                        v___x_1918_ = crate::leanh::lean_box(0);
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_1908_ = crate::leanh::lean_ctor_get(v_a_1904_, 1);
                crate::leanh::lean_inc(v_levelParams_1908_);
                crate::leanh::lean_dec(v_a_1904_);
                v___x_1909_ = crate::leanh::lean_box(0);
                v___x_1910_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__7(v_levelParams_1908_, v___x_1909_);
                v___x_1911_ = l_Lean_mkConst(v_constName_1899_, v___x_1910_);
                if v_isShared_1907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1913_;
            }
            3 => {
                if v_isShared_1919_ == 0 {
                    v___x_1921_ = v___x_1918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3___boxed(
    mut v_constName_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v_constName_1924_, v___y_1925_, v___y_1926_);
    crate::leanh::lean_dec(v___y_1926_);
    crate::leanh::lean_dec_ref(v___y_1925_);
    return v_res_1928_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(
    mut v_x_1929_: *mut crate::leanh::LeanObject,
    mut v_x_1930_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1929_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1930_) == 0 {
            let mut v___x_1931_: u8 = 0;
            v___x_1931_ = 1;
            return v___x_1931_;
        } else {
            let mut v___x_1932_: u8 = 0;
            v___x_1932_ = 0;
            return v___x_1932_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1930_) == 0 {
            let mut v___x_1933_: u8 = 0;
            v___x_1933_ = 0;
            return v___x_1933_;
        } else {
            let mut v_val_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: u8 = 0;
            v_val_1934_ = crate::leanh::lean_ctor_get(v_x_1929_, 0);
            v_val_1935_ = crate::leanh::lean_ctor_get(v_x_1930_, 0);
            v___x_1936_ = lean_name_eq(v_val_1934_, v_val_1935_);
            return v___x_1936_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4___boxed(
    mut v_x_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1939_: u8 = 0;
    let mut v_r_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1939_ = l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(v_x_1937_, v_x_1938_);
    crate::leanh::lean_dec(v_x_1938_);
    crate::leanh::lean_dec(v_x_1937_);
    v_r_1940_ = crate::leanh::lean_box((v_res_1939_) as usize);
    return v_r_1940_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0;
    v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2;
    v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4;
    v___x_1949_ = l_Lean_stringToMessageData(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6;
    v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(
    mut v_declName_1953_: *mut crate::leanh::LeanObject,
    mut v_target_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_unused_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1983_ = lean_st_ref_get(v___y_1956_);
                v_env_1984_ = crate::leanh::lean_ctor_get(v___x_1983_, 0);
                crate::leanh::lean_inc_ref(v_env_1984_);
                crate::leanh::lean_dec(v___x_1983_);
                v___x_1985_ = crate::leanh::lean_box(0);
                v___x_1999_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1984_, v_declName_1953_);
                crate::leanh::lean_dec_ref(v_env_1984_);
                if crate::leanh::lean_obj_tag(v___x_1999_) == 0 {
                    v___x_2000_ = lean_st_ref_get(v___y_1956_);
                    v_env_2001_ = crate::leanh::lean_ctor_get(v___x_2000_, 0);
                    crate::leanh::lean_inc_ref(v_env_2001_);
                    crate::leanh::lean_dec(v___x_2000_);
                    v___x_2002_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
                    v_toEnvExtension_2003_ = crate::leanh::lean_ctor_get(v___x_2002_, 0);
                    v_asyncMode_2004_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2003_, 2);
                    v___x_2005_ = 1;
                    crate::leanh::lean_inc(v_declName_1953_);
                    v___x_2006_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                        v___x_1985_,
                        v___x_2002_,
                        v_env_2001_,
                        v_declName_1953_,
                        v_asyncMode_2004_,
                        v___x_2005_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2006_) == 0 {
                        v___x_2007_ = lean_st_ref_get(v___y_1956_);
                        v_env_2008_ = crate::leanh::lean_ctor_get(v___x_2007_, 0);
                        crate::leanh::lean_inc_ref(v_env_2008_);
                        crate::leanh::lean_dec(v___x_2007_);
                        v_____do__lift_1987_ = v_env_2008_;
                        v___y_1988_ = v___y_1955_;
                        v___y_1989_ = v___y_1956_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2006_, 1);
                        crate::leanh::lean_dec(v_target_1954_);
                        v___x_2009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3);
                        v___x_2010_ = 0;
                        v___x_2011_ = l_Lean_MessageData_ofConstName(v_declName_1953_, v___x_2010_);
                        v___x_2012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2009_);
                        crate::leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
                        v___x_2013_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5);
                        v___x_2014_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                        crate::leanh::lean_ctor_set(v___x_2014_, 1, v___x_2013_);
                        v___x_2015_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2014_, v___y_1955_, v___y_1956_);
                        return v___x_2015_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1999_, 1);
                    crate::leanh::lean_dec(v_target_1954_);
                    v___x_2016_ = 0;
                    v___x_2017_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3);
                    v___x_2018_ = l_Lean_MessageData_ofConstName(v_declName_1953_, v___x_2016_);
                    v___x_2019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
                    crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                    v___x_2020_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7);
                    v___x_2021_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2021_, 0, v___x_2019_);
                    crate::leanh::lean_ctor_set(v___x_2021_, 1, v___x_2020_);
                    v___x_2022_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2021_, v___y_1955_, v___y_1956_);
                    return v___x_2022_;
                }
            }
            1 => {
                v___x_1960_ = lean_st_ref_take(v___y_1959_);
                v_env_1961_ = crate::leanh::lean_ctor_get(v___x_1960_, 0);
                v_nextMacroScope_1962_ = crate::leanh::lean_ctor_get(v___x_1960_, 1);
                v_ngen_1963_ = crate::leanh::lean_ctor_get(v___x_1960_, 2);
                v_auxDeclNGen_1964_ = crate::leanh::lean_ctor_get(v___x_1960_, 3);
                v_traceState_1965_ = crate::leanh::lean_ctor_get(v___x_1960_, 4);
                v_messages_1966_ = crate::leanh::lean_ctor_get(v___x_1960_, 6);
                v_infoState_1967_ = crate::leanh::lean_ctor_get(v___x_1960_, 7);
                v_snapshotTasks_1968_ = crate::leanh::lean_ctor_get(v___x_1960_, 8);
                v_isSharedCheck_1981_ = (!crate::leanh::lean_is_exclusive(v___x_1960_)) as u8;
                if v_isSharedCheck_1981_ == 0 {
                    v_unused_1982_ = crate::leanh::lean_ctor_get(v___x_1960_, 5);
                    crate::leanh::lean_dec(v_unused_1982_);
                    v___x_1970_ = v___x_1960_;
                    v_isShared_1971_ = v_isSharedCheck_1981_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1968_);
                    crate::leanh::lean_inc(v_infoState_1967_);
                    crate::leanh::lean_inc(v_messages_1966_);
                    crate::leanh::lean_inc(v_traceState_1965_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1964_);
                    crate::leanh::lean_inc(v_ngen_1963_);
                    crate::leanh::lean_inc(v_nextMacroScope_1962_);
                    crate::leanh::lean_inc(v_env_1961_);
                    crate::leanh::lean_dec(v___x_1960_);
                    v___x_1970_ = crate::leanh::lean_box(0);
                    v_isShared_1971_ = v_isSharedCheck_1981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1972_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
                v___x_1973_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_1972_,
                    v_env_1961_,
                    v_declName_1953_,
                    v_target_1954_,
                );
                v___x_1974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2);
                if v_isShared_1971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1970_, 5, v___x_1974_);
                    crate::leanh::lean_ctor_set(v___x_1970_, 0, v___x_1973_);
                    v___x_1976_ = v___x_1970_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_nextMacroScope_1962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_ngen_1963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_auxDeclNGen_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 4, v_traceState_1965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 5, v___x_1974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 6, v_messages_1966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 7, v_infoState_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 8, v_snapshotTasks_1968_);
                    v___x_1976_ = v_reuseFailAlloc_1980_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1977_ = lean_st_ref_set(v___y_1959_, v___x_1976_);
                v___x_1978_ = crate::leanh::lean_box(0);
                v___x_1979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1979_, 0, v___x_1978_);
                return v___x_1979_;
            }
            4 => {
                v___x_1990_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
                v_toEnvExtension_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                v_asyncMode_1992_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1991_, 2);
                v___x_1993_ = 1;
                crate::leanh::lean_inc(v_target_1954_);
                v___x_1994_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_1985_,
                    v___x_1990_,
                    v_____do__lift_1987_,
                    v_target_1954_,
                    v_asyncMode_1992_,
                    v___x_1993_,
                );
                crate::leanh::lean_inc(v_declName_1953_);
                v___x_1995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1995_, 0, v_declName_1953_);
                v___x_1996_ = l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(v___x_1994_, v___x_1995_);
                crate::leanh::lean_dec_ref_known(v___x_1995_, 1);
                crate::leanh::lean_dec(v___x_1994_);
                if v___x_1996_ == 0 {
                    v___y_1959_ = v___y_1989_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_target_1954_);
                    crate::leanh::lean_dec(v_declName_1953_);
                    v___x_1997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1);
                    v___x_1998_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_1997_, v___y_1988_, v___y_1989_);
                    return v___x_1998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___boxed(
    mut v_declName_2023_: *mut crate::leanh::LeanObject,
    mut v_target_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_declName_2023_, v_target_2024_, v___y_2025_, v___y_2026_);
    crate::leanh::lean_dec(v___y_2026_);
    crate::leanh::lean_dec_ref(v___y_2025_);
    return v_res_2028_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
    return v___x_2031_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
    return v___x_2034_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
    return v___x_2043_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(
    mut v___x_2047_: *mut crate::leanh::LeanObject,
    mut v___x_2048_: *mut crate::leanh::LeanObject,
    mut v___x_2049_: *mut crate::leanh::LeanObject,
    mut v_decl_2050_: *mut crate::leanh::LeanObject,
    mut v_stx_2051_: *mut crate::leanh::LeanObject,
    mut v_kind_2052_: u8,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2057_: u8 = 0;
    let mut v___y_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v_ref_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v___y_2097_: u8 = 0;
    let mut v___y_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v___y_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2116_: u8 = 0;
    let mut v___y_2118_: u8 = 0;
    let mut v___y_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2135_: u8 = 0;
    let mut v_cancelTk_x3f_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2137_: u8 = 0;
    let mut v_inheritedTraceOptions_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2181_: u8 = 0;
    let mut v_a_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2189_: u8 = 0;
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2218_ = 0;
                v___x_2219_ = l_Lean_instBEqAttributeKind_beq(v_kind_2052_, v___x_2218_);
                if v___x_2219_ == 0 {
                    crate::leanh::lean_dec(v_stx_2051_);
                    crate::leanh::lean_dec(v_decl_2050_);
                    crate::leanh::lean_dec_ref(v___x_2047_);
                    v___x_2220_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v___x_2049_, v_kind_2052_, v___y_2053_, v___y_2054_);
                    return v___x_2220_;
                } else {
                    state = 17;
                    continue;
                }
            }
            1 => {
                v___x_2062_ = lean_st_ref_get(v___y_2061_);
                v_env_2063_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                crate::leanh::lean_inc_ref(v_env_2063_);
                crate::leanh::lean_dec(v___x_2062_);
                crate::leanh::lean_inc(v___y_2060_);
                v___x_2064_ =
                    l_Lean_findInternalDocString_x3f(v_env_2063_, v___y_2060_, v___y_2057_);
                if crate::leanh::lean_obj_tag(v___x_2064_) == 0 {
                    v_a_2065_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                    crate::leanh::lean_inc(v_a_2065_);
                    crate::leanh::lean_dec_ref_known(v___x_2064_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2065_) == 0 {
                        if v___y_2057_ == 0 {
                            crate::leanh::lean_dec(v___y_2059_);
                            v___x_2066_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                            crate::leanh::lean_dec_ref(v___y_2058_);
                            return v___x_2066_;
                        } else {
                            crate::leanh::lean_inc(v___y_2060_);
                            v___x_2067_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v___y_2060_, v___y_2058_, v___y_2061_);
                            if crate::leanh::lean_obj_tag(v___x_2067_) == 0 {
                                v_a_2068_ = crate::leanh::lean_ctor_get(v___x_2067_, 0);
                                crate::leanh::lean_inc(v_a_2068_);
                                crate::leanh::lean_dec_ref_known(v___x_2067_, 1);
                                v___x_2069_ = l_Lean_MessageData_ofExpr(v_a_2068_);
                                v___x_2070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                v___x_2071_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2071_, 0, v___x_2069_);
                                crate::leanh::lean_ctor_set(v___x_2071_, 1, v___x_2070_);
                                v___x_2072_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(v___y_2059_, v___x_2071_, v___y_2058_, v___y_2061_);
                                crate::leanh::lean_dec(v___y_2059_);
                                if crate::leanh::lean_obj_tag(v___x_2072_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2072_, 1);
                                    v___x_2073_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                                    crate::leanh::lean_dec_ref(v___y_2058_);
                                    return v___x_2073_;
                                } else {
                                    crate::leanh::lean_dec(v___y_2060_);
                                    crate::leanh::lean_dec_ref(v___y_2058_);
                                    crate::leanh::lean_dec(v_decl_2050_);
                                    return v___x_2072_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___y_2060_);
                                crate::leanh::lean_dec(v___y_2059_);
                                crate::leanh::lean_dec_ref(v___y_2058_);
                                crate::leanh::lean_dec(v_decl_2050_);
                                v_a_2074_ = crate::leanh::lean_ctor_get(v___x_2067_, 0);
                                v_isSharedCheck_2081_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2067_)) as u8;
                                if v_isSharedCheck_2081_ == 0 {
                                    v___x_2076_ = v___x_2067_;
                                    v_isShared_2077_ = v_isSharedCheck_2081_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2074_);
                                    crate::leanh::lean_dec(v___x_2067_);
                                    v___x_2076_ = crate::leanh::lean_box(0);
                                    v_isShared_2077_ = v_isSharedCheck_2081_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_2065_, 1);
                        crate::leanh::lean_dec(v___y_2059_);
                        v___x_2082_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                        crate::leanh::lean_dec_ref(v___y_2058_);
                        return v___x_2082_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2060_);
                    crate::leanh::lean_dec(v___y_2059_);
                    crate::leanh::lean_dec(v_decl_2050_);
                    v_a_2083_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                    v_isSharedCheck_2095_ = (!crate::leanh::lean_is_exclusive(v___x_2064_)) as u8;
                    if v_isSharedCheck_2095_ == 0 {
                        v___x_2085_ = v___x_2064_;
                        v_isShared_2086_ = v_isSharedCheck_2095_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2083_);
                        crate::leanh::lean_dec(v___x_2064_);
                        v___x_2085_ = crate::leanh::lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2095_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2077_ == 0 {
                    v___x_2079_ = v___x_2076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2080_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
                    v___x_2079_ = v_reuseFailAlloc_2080_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2079_;
            }
            4 => {
                v_ref_2087_ = crate::leanh::lean_ctor_get(v___y_2058_, 5);
                crate::leanh::lean_inc(v_ref_2087_);
                crate::leanh::lean_dec_ref(v___y_2058_);
                v___x_2088_ = lean_io_error_to_string(v_a_2083_);
                v___x_2089_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2088_);
                v___x_2090_ = l_Lean_MessageData_ofFormat(v___x_2089_);
                v___x_2091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2091_, 0, v_ref_2087_);
                crate::leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
                if v_isShared_2086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2091_);
                    v___x_2093_ = v___x_2085_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
                    v___x_2093_ = v_reuseFailAlloc_2094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2093_;
            }
            6 => {
                v___x_2103_ = l_Lean_Elab_inServer;
                v___x_2104_ = l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(v___y_2099_, v___x_2103_);
                crate::leanh::lean_dec_ref(v___y_2099_);
                if v___x_2104_ == 0 {
                    crate::leanh::lean_dec(v___y_2100_);
                    v___x_2105_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2102_, v___y_2098_, v___y_2101_);
                    crate::leanh::lean_dec_ref(v___y_2098_);
                    return v___x_2105_;
                } else {
                    v___y_2057_ = v___y_2097_;
                    v___y_2058_ = v___y_2098_;
                    v___y_2059_ = v___y_2100_;
                    v___y_2060_ = v___y_2102_;
                    v___y_2061_ = v___y_2101_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2112_ = lean_st_ref_get(v___y_2111_);
                v_env_2113_ = crate::leanh::lean_ctor_get(v___x_2112_, 0);
                crate::leanh::lean_inc_ref(v_env_2113_);
                crate::leanh::lean_dec(v___x_2112_);
                v_options_2114_ = crate::leanh::lean_ctor_get(v___y_2110_, 2);
                v___x_2115_ = l_Lean_Environment_header(v_env_2113_);
                crate::leanh::lean_dec_ref(v_env_2113_);
                v_isModule_2116_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2115_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_2115_);
                if v_isModule_2116_ == 0 {
                    if v___y_2107_ == 0 {
                        crate::leanh::lean_inc_ref(v_options_2114_);
                        v___y_2097_ = v___y_2107_;
                        v___y_2098_ = v___y_2110_;
                        v___y_2099_ = v_options_2114_;
                        v___y_2100_ = v___y_2108_;
                        v___y_2101_ = v___y_2111_;
                        v___y_2102_ = v___y_2109_;
                        state = 6;
                        continue;
                    } else {
                        v___y_2057_ = v___y_2107_;
                        v___y_2058_ = v___y_2110_;
                        v___y_2059_ = v___y_2108_;
                        v___y_2060_ = v___y_2109_;
                        v___y_2061_ = v___y_2111_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_options_2114_);
                    v___y_2097_ = v___y_2107_;
                    v___y_2098_ = v___y_2110_;
                    v___y_2099_ = v_options_2114_;
                    v___y_2100_ = v___y_2108_;
                    v___y_2101_ = v___y_2111_;
                    v___y_2102_ = v___y_2109_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v_fileName_2123_ = crate::leanh::lean_ctor_get(v___y_2121_, 0);
                v_fileMap_2124_ = crate::leanh::lean_ctor_get(v___y_2121_, 1);
                v_options_2125_ = crate::leanh::lean_ctor_get(v___y_2121_, 2);
                v_currRecDepth_2126_ = crate::leanh::lean_ctor_get(v___y_2121_, 3);
                v_maxRecDepth_2127_ = crate::leanh::lean_ctor_get(v___y_2121_, 4);
                v_ref_2128_ = crate::leanh::lean_ctor_get(v___y_2121_, 5);
                v_currNamespace_2129_ = crate::leanh::lean_ctor_get(v___y_2121_, 6);
                v_openDecls_2130_ = crate::leanh::lean_ctor_get(v___y_2121_, 7);
                v_initHeartbeats_2131_ = crate::leanh::lean_ctor_get(v___y_2121_, 8);
                v_maxHeartbeats_2132_ = crate::leanh::lean_ctor_get(v___y_2121_, 9);
                v_quotContext_2133_ = crate::leanh::lean_ctor_get(v___y_2121_, 10);
                v_currMacroScope_2134_ = crate::leanh::lean_ctor_get(v___y_2121_, 11);
                v_diag_2135_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2121_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2136_ = crate::leanh::lean_ctor_get(v___y_2121_, 12);
                v_suppressElabErrors_2137_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2121_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2138_ = crate::leanh::lean_ctor_get(v___y_2121_, 13);
                v_ref_2139_ = l_Lean_replaceRef(v___y_2119_, v_ref_2128_);
                crate::leanh::lean_dec(v___y_2119_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2138_);
                crate::leanh::lean_inc(v_cancelTk_x3f_2136_);
                crate::leanh::lean_inc(v_currMacroScope_2134_);
                crate::leanh::lean_inc(v_quotContext_2133_);
                crate::leanh::lean_inc(v_maxHeartbeats_2132_);
                crate::leanh::lean_inc(v_initHeartbeats_2131_);
                crate::leanh::lean_inc(v_openDecls_2130_);
                crate::leanh::lean_inc(v_currNamespace_2129_);
                crate::leanh::lean_inc(v_ref_2139_);
                crate::leanh::lean_inc(v_maxRecDepth_2127_);
                crate::leanh::lean_inc(v_currRecDepth_2126_);
                crate::leanh::lean_inc_ref(v_options_2125_);
                crate::leanh::lean_inc_ref(v_fileMap_2124_);
                crate::leanh::lean_inc_ref(v_fileName_2123_);
                v___x_2140_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2140_, 0, v_fileName_2123_);
                crate::leanh::lean_ctor_set(v___x_2140_, 1, v_fileMap_2124_);
                crate::leanh::lean_ctor_set(v___x_2140_, 2, v_options_2125_);
                crate::leanh::lean_ctor_set(v___x_2140_, 3, v_currRecDepth_2126_);
                crate::leanh::lean_ctor_set(v___x_2140_, 4, v_maxRecDepth_2127_);
                crate::leanh::lean_ctor_set(v___x_2140_, 5, v_ref_2139_);
                crate::leanh::lean_ctor_set(v___x_2140_, 6, v_currNamespace_2129_);
                crate::leanh::lean_ctor_set(v___x_2140_, 7, v_openDecls_2130_);
                crate::leanh::lean_ctor_set(v___x_2140_, 8, v_initHeartbeats_2131_);
                crate::leanh::lean_ctor_set(v___x_2140_, 9, v_maxHeartbeats_2132_);
                crate::leanh::lean_ctor_set(v___x_2140_, 10, v_quotContext_2133_);
                crate::leanh::lean_ctor_set(v___x_2140_, 11, v_currMacroScope_2134_);
                crate::leanh::lean_ctor_set(v___x_2140_, 12, v_cancelTk_x3f_2136_);
                crate::leanh::lean_ctor_set(v___x_2140_, 13, v_inheritedTraceOptions_2138_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2140_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_2135_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2140_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2137_,
                );
                if crate::leanh::lean_obj_tag(v_id_x3f_2120_) == 1 {
                    v_val_2141_ = crate::leanh::lean_ctor_get(v_id_x3f_2120_, 0);
                    v_isSharedCheck_2190_ =
                        (!crate::leanh::lean_is_exclusive(v_id_x3f_2120_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2143_ = v_id_x3f_2120_;
                        v_isShared_2144_ = v_isSharedCheck_2190_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2141_);
                        crate::leanh::lean_dec(v_id_x3f_2120_);
                        v___x_2143_ = crate::leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2190_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ref_2139_);
                    crate::leanh::lean_dec(v_id_x3f_2120_);
                    crate::leanh::lean_dec(v_decl_2050_);
                    v___x_2191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                    v___x_2192_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2191_, v___x_2140_, v___y_2122_);
                    crate::leanh::lean_dec_ref_known(v___x_2140_, 14);
                    return v___x_2192_;
                }
            }
            9 => {
                v___x_2145_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_val_2141_);
                v___x_2146_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_2146_, 0, v_val_2141_);
                crate::leanh::lean_closure_set(v___x_2146_, 1, v___x_2145_);
                v___x_2147_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v___x_2146_, v___y_2118_, v___x_2140_, v___y_2122_);
                if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                    v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                    crate::leanh::lean_inc(v_a_2148_);
                    crate::leanh::lean_dec_ref_known(v___x_2147_, 1);
                    v___x_2149_ = lean_st_ref_get(v___y_2122_);
                    v_env_2150_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    crate::leanh::lean_inc_ref(v_env_2150_);
                    crate::leanh::lean_dec(v___x_2149_);
                    v___x_2151_ = 0;
                    crate::leanh::lean_inc(v_decl_2050_);
                    v___x_2152_ =
                        l_Lean_findSimpleDocString_x3f(v_env_2150_, v_decl_2050_, v___x_2151_);
                    if crate::leanh::lean_obj_tag(v___x_2152_) == 0 {
                        crate::leanh::lean_del_object(v___x_2143_);
                        crate::leanh::lean_dec(v_ref_2139_);
                        v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                        crate::leanh::lean_inc(v_a_2153_);
                        crate::leanh::lean_dec_ref_known(v___x_2152_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2153_) == 0 {
                            v___y_2107_ = v___y_2118_;
                            v___y_2108_ = v_val_2141_;
                            v___y_2109_ = v_a_2148_;
                            v___y_2110_ = v___x_2140_;
                            v___y_2111_ = v___y_2122_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_2153_, 1);
                            if v___y_2118_ == 0 {
                                v___y_2107_ = v___y_2118_;
                                v___y_2108_ = v_val_2141_;
                                v___y_2109_ = v_a_2148_;
                                v___y_2110_ = v___x_2140_;
                                v___y_2111_ = v___y_2122_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_decl_2050_);
                                v___x_2154_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v_decl_2050_, v___x_2140_, v___y_2122_);
                                if crate::leanh::lean_obj_tag(v___x_2154_) == 0 {
                                    v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2154_, 0);
                                    crate::leanh::lean_inc(v_a_2155_);
                                    crate::leanh::lean_dec_ref_known(v___x_2154_, 1);
                                    v___x_2156_ = l_Lean_MessageData_ofExpr(v_a_2155_);
                                    v___x_2157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                    v___x_2158_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v___x_2156_);
                                    crate::leanh::lean_ctor_set(v___x_2158_, 1, v___x_2157_);
                                    v___x_2159_ = l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(v___x_2158_, v___x_2140_, v___y_2122_);
                                    if crate::leanh::lean_obj_tag(v___x_2159_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2159_, 1);
                                        v___y_2107_ = v___y_2118_;
                                        v___y_2108_ = v_val_2141_;
                                        v___y_2109_ = v_a_2148_;
                                        v___y_2110_ = v___x_2140_;
                                        v___y_2111_ = v___y_2122_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2148_);
                                        crate::leanh::lean_dec(v_val_2141_);
                                        crate::leanh::lean_dec_ref_known(v___x_2140_, 14);
                                        crate::leanh::lean_dec(v_decl_2050_);
                                        return v___x_2159_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2148_);
                                    crate::leanh::lean_dec(v_val_2141_);
                                    crate::leanh::lean_dec_ref_known(v___x_2140_, 14);
                                    crate::leanh::lean_dec(v_decl_2050_);
                                    v_a_2160_ = crate::leanh::lean_ctor_get(v___x_2154_, 0);
                                    v_isSharedCheck_2167_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2154_)) as u8;
                                    if v_isSharedCheck_2167_ == 0 {
                                        v___x_2162_ = v___x_2154_;
                                        v_isShared_2163_ = v_isSharedCheck_2167_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2160_);
                                        crate::leanh::lean_dec(v___x_2154_);
                                        v___x_2162_ = crate::leanh::lean_box(0);
                                        v_isShared_2163_ = v_isSharedCheck_2167_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2148_);
                        crate::leanh::lean_dec(v_val_2141_);
                        crate::leanh::lean_dec_ref_known(v___x_2140_, 14);
                        crate::leanh::lean_dec(v_decl_2050_);
                        v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                        v_isSharedCheck_2181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2152_)) as u8;
                        if v_isSharedCheck_2181_ == 0 {
                            v___x_2170_ = v___x_2152_;
                            v_isShared_2171_ = v_isSharedCheck_2181_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2168_);
                            crate::leanh::lean_dec(v___x_2152_);
                            v___x_2170_ = crate::leanh::lean_box(0);
                            v_isShared_2171_ = v_isSharedCheck_2181_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2143_);
                    crate::leanh::lean_dec(v_val_2141_);
                    crate::leanh::lean_dec_ref_known(v___x_2140_, 14);
                    crate::leanh::lean_dec(v_ref_2139_);
                    crate::leanh::lean_dec(v_decl_2050_);
                    v_a_2182_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                    v_isSharedCheck_2189_ = (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                    if v_isSharedCheck_2189_ == 0 {
                        v___x_2184_ = v___x_2147_;
                        v_isShared_2185_ = v_isSharedCheck_2189_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2182_);
                        crate::leanh::lean_dec(v___x_2147_);
                        v___x_2184_ = crate::leanh::lean_box(0);
                        v_isShared_2185_ = v_isSharedCheck_2189_;
                        state = 15;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2163_ == 0 {
                    v___x_2165_ = v___x_2162_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
                    v___x_2165_ = v_reuseFailAlloc_2166_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2165_;
            }
            12 => {
                v___x_2172_ = lean_io_error_to_string(v_a_2168_);
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2143_, 3);
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2172_);
                    v___x_2174_ = v___x_2143_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2172_);
                    v___x_2174_ = v_reuseFailAlloc_2180_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2175_ = l_Lean_MessageData_ofFormat(v___x_2174_);
                v___x_2176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2176_, 0, v_ref_2139_);
                crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2175_);
                if v_isShared_2171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2170_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                    v___x_2178_ = v_reuseFailAlloc_2179_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2178_;
            }
            15 => {
                if v_isShared_2185_ == 0 {
                    v___x_2187_ = v___x_2184_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
                    v___x_2187_ = v_reuseFailAlloc_2188_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2187_;
            }
            17 => {
                v___x_2194_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
                v___x_2195_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
                v___x_2196_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
                v___x_2197_ =
                    l_Lean_Name_mkStr4(v___x_2047_, v___x_2194_, v___x_2195_, v___x_2196_);
                crate::leanh::lean_inc(v_stx_2051_);
                v___x_2198_ = l_Lean_Syntax_isOfKind(v_stx_2051_, v___x_2197_);
                crate::leanh::lean_dec(v___x_2197_);
                if v___x_2198_ == 0 {
                    crate::leanh::lean_dec(v_stx_2051_);
                    crate::leanh::lean_dec(v_decl_2050_);
                    crate::leanh::lean_dec(v___x_2049_);
                    v___x_2199_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                    v___x_2200_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2199_, v___y_2053_, v___y_2054_);
                    return v___x_2200_;
                } else {
                    v___x_2201_ = l_Lean_Syntax_getArg(v_stx_2051_, v___x_2048_);
                    v___x_2202_ = l_Lean_Syntax_matchesIdent(v___x_2201_, v___x_2049_);
                    if v___x_2202_ == 0 {
                        crate::leanh::lean_dec(v___x_2201_);
                        crate::leanh::lean_dec(v_stx_2051_);
                        crate::leanh::lean_dec(v_decl_2050_);
                        v___x_2203_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                        v___x_2204_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2203_, v___y_2053_, v___y_2054_);
                        return v___x_2204_;
                    } else {
                        v___x_2205_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2206_ = l_Lean_Syntax_getArg(v_stx_2051_, v___x_2205_);
                        crate::leanh::lean_dec(v_stx_2051_);
                        v___x_2207_ = l_Lean_Syntax_isNone(v___x_2206_);
                        if v___x_2207_ == 0 {
                            crate::leanh::lean_inc(v___x_2206_);
                            v___x_2208_ = l_Lean_Syntax_matchesNull(v___x_2206_, v___x_2205_);
                            if v___x_2208_ == 0 {
                                crate::leanh::lean_dec(v___x_2206_);
                                crate::leanh::lean_dec(v___x_2201_);
                                crate::leanh::lean_dec(v_decl_2050_);
                                v___x_2209_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                v___x_2210_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2209_, v___y_2053_, v___y_2054_);
                                return v___x_2210_;
                            } else {
                                v_id_x3f_2211_ = l_Lean_Syntax_getArg(v___x_2206_, v___x_2048_);
                                crate::leanh::lean_dec(v___x_2206_);
                                v___x_2212_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
                                crate::leanh::lean_inc(v_id_x3f_2211_);
                                v___x_2213_ = l_Lean_Syntax_isOfKind(v_id_x3f_2211_, v___x_2212_);
                                if v___x_2213_ == 0 {
                                    crate::leanh::lean_dec(v_id_x3f_2211_);
                                    crate::leanh::lean_dec(v___x_2201_);
                                    crate::leanh::lean_dec(v_decl_2050_);
                                    v___x_2214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                    v___x_2215_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2214_, v___y_2053_, v___y_2054_);
                                    return v___x_2215_;
                                } else {
                                    v___x_2216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2216_, 0, v_id_x3f_2211_);
                                    v___y_2118_ = v___x_2202_;
                                    v___y_2119_ = v___x_2201_;
                                    v_id_x3f_2120_ = v___x_2216_;
                                    v___y_2121_ = v___y_2053_;
                                    v___y_2122_ = v___y_2054_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2206_);
                            v___x_2217_ = crate::leanh::lean_box(0);
                            v___y_2118_ = v___x_2202_;
                            v___y_2119_ = v___x_2201_;
                            v_id_x3f_2120_ = v___x_2217_;
                            v___y_2121_ = v___y_2053_;
                            v___y_2122_ = v___y_2054_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v___x_2221_: *mut crate::leanh::LeanObject,
    mut v___x_2222_: *mut crate::leanh::LeanObject,
    mut v___x_2223_: *mut crate::leanh::LeanObject,
    mut v_decl_2224_: *mut crate::leanh::LeanObject,
    mut v_stx_2225_: *mut crate::leanh::LeanObject,
    mut v_kind_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2230_: u8 = 0;
    let mut v_res_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2230_ = (crate::leanh::lean_unbox(v_kind_2226_) as u8);
    v_res_2231_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(v___x_2221_, v___x_2222_, v___x_2223_, v_decl_2224_, v_stx_2225_, v_kind_boxed_2230_, v___y_2227_, v___y_2228_);
    crate::leanh::lean_dec(v___y_2228_);
    crate::leanh::lean_dec_ref(v___y_2227_);
    crate::leanh::lean_dec(v___x_2222_);
    return v_res_2231_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
    return v___x_2234_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(
    mut v___x_2238_: *mut crate::leanh::LeanObject,
    mut v_decl_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
    v___x_2244_ = l_Lean_MessageData_ofName(v___x_2238_);
    v___x_2245_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
    crate::leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
    v___x_2246_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
    v___x_2247_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2245_);
    crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2246_);
    v___x_2248_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2247_, v___y_2240_, v___y_2241_);
    return v___x_2248_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v___x_2249_: *mut crate::leanh::LeanObject,
    mut v_decl_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(v___x_2249_, v_decl_2250_, v___y_2251_, v___y_2252_);
    crate::leanh::lean_dec(v___y_2252_);
    crate::leanh::lean_dec_ref(v___y_2251_);
    crate::leanh::lean_dec(v_decl_2250_);
    return v_res_2254_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2328_ = l_Lean_registerBuiltinAttribute(v___x_2327_);
    return v___x_2328_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v_a_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    return v_res_2330_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2331_: *mut crate::leanh::LeanObject,
    mut v_msg_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_2332_, v___y_2333_, v___y_2334_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2337_: *mut crate::leanh::LeanObject,
    mut v_msg_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0(v_00_u03b1_2337_, v_msg_2338_, v___y_2339_, v___y_2340_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b1_2343_: *mut crate::leanh::LeanObject,
    mut v_x_2344_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2345_: u8,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2344_, v_isExporting_2345_, v___y_2346_, v___y_2347_);
    return v___x_2349_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b1_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2356_: u8 = 0;
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2356_ = (crate::leanh::lean_unbox(v_isExporting_2352_) as u8);
    v_res_2357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_2350_, v_x_2351_, v_isExporting_boxed_2356_, v___y_2353_, v___y_2354_);
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2358_: *mut crate::leanh::LeanObject,
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_when_2360_: u8,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v_x_2359_, v_when_2360_, v___y_2361_, v___y_2362_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2365_: *mut crate::leanh::LeanObject,
    mut v_x_2366_: *mut crate::leanh::LeanObject,
    mut v_when_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_2371_: u8 = 0;
    let mut v_res_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2371_ = (crate::leanh::lean_unbox(v_when_2367_) as u8);
    v_res_2372_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1(v_00_u03b1_2365_, v_x_2366_, v_when_boxed_2371_, v___y_2368_, v___y_2369_);
    crate::leanh::lean_dec(v___y_2369_);
    crate::leanh::lean_dec_ref(v___y_2368_);
    return v_res_2372_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7(
    mut v_00_u03b1_2373_: *mut crate::leanh::LeanObject,
    mut v_name_2374_: *mut crate::leanh::LeanObject,
    mut v_kind_2375_: u8,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v_name_2374_, v_kind_2375_, v___y_2376_, v___y_2377_);
    return v___x_2379_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___boxed(
    mut v_00_u03b1_2380_: *mut crate::leanh::LeanObject,
    mut v_name_2381_: *mut crate::leanh::LeanObject,
    mut v_kind_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2386_: u8 = 0;
    let mut v_res_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2386_ = (crate::leanh::lean_unbox(v_kind_2382_) as u8);
    v_res_2387_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7(v_00_u03b1_2380_, v_name_2381_, v_kind_boxed_2386_, v___y_2383_, v___y_2384_);
    crate::leanh::lean_dec(v___y_2384_);
    crate::leanh::lean_dec_ref(v___y_2383_);
    return v_res_2387_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8(
    mut v_00_u03b1_2388_: *mut crate::leanh::LeanObject,
    mut v_constName_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_2389_, v___y_2390_, v___y_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b1_2394_: *mut crate::leanh::LeanObject,
    mut v_constName_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8(v_00_u03b1_2394_, v_constName_2395_, v___y_2396_, v___y_2397_);
    crate::leanh::lean_dec(v___y_2397_);
    crate::leanh::lean_dec_ref(v___y_2396_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12(
    mut v_00_u03b1_2400_: *mut crate::leanh::LeanObject,
    mut v_ref_2401_: *mut crate::leanh::LeanObject,
    mut v_constName_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_2401_, v_constName_2402_, v___y_2403_, v___y_2404_);
    return v___x_2406_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___boxed(
    mut v_00_u03b1_2407_: *mut crate::leanh::LeanObject,
    mut v_ref_2408_: *mut crate::leanh::LeanObject,
    mut v_constName_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12(v_00_u03b1_2407_, v_ref_2408_, v_constName_2409_, v___y_2410_, v___y_2411_);
    crate::leanh::lean_dec(v___y_2411_);
    crate::leanh::lean_dec_ref(v___y_2410_);
    crate::leanh::lean_dec(v_ref_2408_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16(
    mut v_00_u03b1_2414_: *mut crate::leanh::LeanObject,
    mut v_ref_2415_: *mut crate::leanh::LeanObject,
    mut v_msg_2416_: *mut crate::leanh::LeanObject,
    mut v_declHint_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_2415_, v_msg_2416_, v_declHint_2417_, v___y_2418_, v___y_2419_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___boxed(
    mut v_00_u03b1_2422_: *mut crate::leanh::LeanObject,
    mut v_ref_2423_: *mut crate::leanh::LeanObject,
    mut v_msg_2424_: *mut crate::leanh::LeanObject,
    mut v_declHint_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16(v_00_u03b1_2422_, v_ref_2423_, v_msg_2424_, v_declHint_2425_, v___y_2426_, v___y_2427_);
    crate::leanh::lean_dec(v___y_2427_);
    crate::leanh::lean_dec_ref(v___y_2426_);
    crate::leanh::lean_dec(v_ref_2423_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18(
    mut v_msg_2430_: *mut crate::leanh::LeanObject,
    mut v_declHint_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_2430_, v_declHint_2431_, v___y_2433_);
    return v___x_2435_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___boxed(
    mut v_msg_2436_: *mut crate::leanh::LeanObject,
    mut v_declHint_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18(v_msg_2436_, v_declHint_2437_, v___y_2438_, v___y_2439_);
    crate::leanh::lean_dec(v___y_2439_);
    crate::leanh::lean_dec_ref(v___y_2438_);
    return v_res_2441_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18(
    mut v_00_u03b1_2442_: *mut crate::leanh::LeanObject,
    mut v_ref_2443_: *mut crate::leanh::LeanObject,
    mut v_msg_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_2443_, v_msg_2444_, v___y_2445_, v___y_2446_);
    return v___x_2448_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___boxed(
    mut v_00_u03b1_2449_: *mut crate::leanh::LeanObject,
    mut v_ref_2450_: *mut crate::leanh::LeanObject,
    mut v_msg_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18(v_00_u03b1_2449_, v_ref_2450_, v_msg_2451_, v___y_2452_, v___y_2453_);
    crate::leanh::lean_dec(v___y_2453_);
    crate::leanh::lean_dec_ref(v___y_2452_);
    crate::leanh::lean_dec(v_ref_2450_);
    return v_res_2455_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2459_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2460_ = l_Lean_addBuiltinDocString(v___x_2458_, v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    return v_res_2462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InheritDoc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InheritDoc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InheritDoc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InheritDoc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InheritDoc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_InheritDoc(builtin);
}
