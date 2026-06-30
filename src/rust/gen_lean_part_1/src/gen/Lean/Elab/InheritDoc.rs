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
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 99, 121, 99, 108, 101, 32, 100, 101, 116, 101, 99, 116, 101, 100, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 97, 108, 114, 101, 97, 100, 121, 32, 104, 97, 115, 32, 97, 110, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [32, 97, 108, 114, 101, 97, 100, 121, 32, 104, 97, 115, 32, 97, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<62> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 58, 32, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 105, 110, 102, 101, 114, 32, 100, 111, 99, 32, 115, 111, 117, 114, 99, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<41> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [73, 110, 104, 101, 114, 105, 116, 68, 111, 99, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16523336232899777337 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__6_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,3361983042095182364 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__7_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9588181330932994109 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__8_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9935067116431792180 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__11_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2937937637890837981 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1913205937357475176 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__13_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0_value) as *mut leanh::LeanObject,13727712315849183762 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__14_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17495018376186380235 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__15_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 986682242 as usize) << 1) | 1) as *mut leanh::LeanObject,9754258626469971871 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__16_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__17_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12835772358407075316 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__18_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__19_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18022824350782341408 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__20_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,1147403744356159889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__22_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11976168950125103187 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanClosureObject<3> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [105, 110, 104, 101, 114, 105, 116, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__23_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__26_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__27_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__24_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__25_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value: leanh::LeanStringObject<139> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 139, m_capacity: 139, m_length: 138, m_data: [85, 115, 101, 115, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 10, 10, 96, 64, 91, 105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 32, 100, 101, 99, 108, 93, 96, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 110, 104, 101, 114, 105, 116, 32, 116, 104, 101, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 100, 101, 99, 108, 96, 46, 10, 0]};
static mut l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(
    mut v_opts_1232_: *mut leanh::LeanObject,
    mut v_opt_1233_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1234_ = leanh::lean_ctor_get(v_opt_1233_, 0);
    v_defValue_1235_ = leanh::lean_ctor_get(v_opt_1233_, 1);
    v_map_1236_ = leanh::lean_ctor_get(v_opts_1232_, 0);
    v___x_1237_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1236_,
            v_name_1234_,
        );
    if leanh::lean_obj_tag(v___x_1237_) == 0 {
        let mut v___x_1238_: u8 = 0;
        v___x_1238_ = (leanh::lean_unbox(v_defValue_1235_) as u8);
        return v___x_1238_;
    } else {
        let mut v_val_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1239_ = leanh::lean_ctor_get(v___x_1237_, 0);
        leanh::lean_inc(v_val_1239_);
        leanh::lean_dec_ref_known(v___x_1237_, 1);
        if leanh::lean_obj_tag(v_val_1239_) == 1 {
            let mut v_v_1240_: u8 = 0;
            v_v_1240_ = leanh::lean_ctor_get_uint8(v_val_1239_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1239_, 0);
            return v_v_1240_;
        } else {
            let mut v___x_1241_: u8 = 0;
            leanh::lean_dec(v_val_1239_);
            v___x_1241_ = (leanh::lean_unbox(v_defValue_1235_) as u8);
            return v___x_1241_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5___boxed(
    mut v_opts_1242_: *mut leanh::LeanObject,
    mut v_opt_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1244_: u8 = 0;
    let mut v_r_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Lean_Option_get___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__5(v_opts_1242_, v_opt_1243_);
    leanh::lean_dec_ref(v_opt_1243_);
    leanh::lean_dec_ref(v_opts_1242_);
    v_r_1245_ = leanh::lean_box((v_res_1244_) as usize);
    return v_r_1245_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1246_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_1248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1250_ = leanh::lean_unsigned_to_nat(0);
    v___x_1251_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 1, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 2, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 3, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 4, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 5, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 6, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 7, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 8, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 9, v___x_1249_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = leanh::lean_unsigned_to_nat(32);
    v___x_1253_ = lean_mk_empty_array_with_capacity(v___x_1252_);
    v___x_1254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1254_, 0, v___x_1253_);
    return v___x_1254_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = 5usize;
    v___x_1256_ = leanh::lean_unsigned_to_nat(0);
    v___x_1257_ = leanh::lean_unsigned_to_nat(32);
    v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
    v___x_1259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_1260_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1260_, 0, v___x_1259_);
    leanh::lean_ctor_set(v___x_1260_, 1, v___x_1258_);
    leanh::lean_ctor_set(v___x_1260_, 2, v___x_1256_);
    leanh::lean_ctor_set(v___x_1260_, 3, v___x_1256_);
    leanh::lean_ctor_set_usize(v___x_1260_, 4, v___x_1255_);
    return v___x_1260_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = leanh::lean_box(1);
    v___x_1262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_1263_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1264_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 1, v___x_1262_);
    leanh::lean_ctor_set(v___x_1264_, 2, v___x_1261_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = lean_st_ref_get(v___y_1267_);
    v_env_1270_ = leanh::lean_ctor_get(v___x_1269_, 0);
    leanh::lean_inc_ref(v_env_1270_);
    leanh::lean_dec(v___x_1269_);
    v_options_1271_ = leanh::lean_ctor_get(v___y_1266_, 2);
    v___x_1272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_1273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_1271_);
    v___x_1274_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1274_, 0, v_env_1270_);
    leanh::lean_ctor_set(v___x_1274_, 1, v___x_1272_);
    leanh::lean_ctor_set(v___x_1274_, 2, v___x_1273_);
    leanh::lean_ctor_set(v___x_1274_, 3, v_options_1271_);
    v___x_1275_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
    leanh::lean_ctor_set(v___x_1275_, 1, v_msgData_1265_);
    v___x_1276_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1276_, 0, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1277_, v___y_1278_, v___y_1279_);
    leanh::lean_dec(v___y_1279_);
    leanh::lean_dec_ref(v___y_1278_);
    return v_res_1281_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0(
    mut v___y_1290_: u8,
    mut v_suppressElabErrors_1291_: u8,
    mut v_x_1292_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1292_) == 1 {
        let mut v_pre_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_1293_ = leanh::lean_ctor_get(v_x_1292_, 0);
        match leanh::lean_obj_tag(v_pre_1293_) {
            1 => {
                let mut v_pre_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_1294_ = leanh::lean_ctor_get(v_pre_1293_, 0);
                match leanh::lean_obj_tag(v_pre_1294_) {
                    0 => {
                        let mut v_str_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1298_: u8 = 0;
                        v_str_1295_ = leanh::lean_ctor_get(v_x_1292_, 1);
                        v_str_1296_ = leanh::lean_ctor_get(v_pre_1293_, 1);
                        v___x_1297_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__0;
                        v___x_1298_ = lean_string_dec_eq(v_str_1296_, v___x_1297_);
                        if v___x_1298_ == 0 {
                            let mut v___x_1299_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1300_: u8 = 0;
                            v___x_1299_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__1;
                            v___x_1300_ = lean_string_dec_eq(v_str_1296_, v___x_1299_);
                            if v___x_1300_ == 0 {
                                return v___y_1290_;
                            } else {
                                let mut v___x_1301_: *mut leanh::LeanObject =
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
                            let mut v___x_1303_: *mut leanh::LeanObject =
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
                        let mut v_pre_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1305_ = leanh::lean_ctor_get(v_pre_1294_, 0);
                        if leanh::lean_obj_tag(v_pre_1305_) == 0 {
                            let mut v_str_1306_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1307_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1308_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1309_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1310_: u8 = 0;
                            v_str_1306_ = leanh::lean_ctor_get(v_x_1292_, 1);
                            v_str_1307_ = leanh::lean_ctor_get(v_pre_1293_, 1);
                            v_str_1308_ = leanh::lean_ctor_get(v_pre_1294_, 1);
                            v___x_1309_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__4;
                            v___x_1310_ = lean_string_dec_eq(v_str_1308_, v___x_1309_);
                            if v___x_1310_ == 0 {
                                return v___y_1290_;
                            } else {
                                let mut v___x_1311_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1312_: u8 = 0;
                                v___x_1311_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___closed__5;
                                v___x_1312_ = lean_string_dec_eq(v_str_1307_, v___x_1311_);
                                if v___x_1312_ == 0 {
                                    return v___y_1290_;
                                } else {
                                    let mut v___x_1313_: *mut leanh::LeanObject =
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
                let mut v_str_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1317_: u8 = 0;
                v_str_1315_ = leanh::lean_ctor_get(v_x_1292_, 1);
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
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_1319_: *mut leanh::LeanObject,
    mut v_x_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_11738__boxed_1321_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1322_: u8 = 0;
    let mut v_res_1323_: u8 = 0;
    let mut v_r_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_11738__boxed_1321_ = (leanh::lean_unbox(v___y_1318_) as u8);
    v_suppressElabErrors_boxed_1322_ = (leanh::lean_unbox(v_suppressElabErrors_1319_) as u8);
    v_res_1323_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0(v___y_11738__boxed_1321_, v_suppressElabErrors_boxed_1322_, v_x_1320_);
    leanh::lean_dec(v_x_1320_);
    v_r_1324_ = leanh::lean_box((v_res_1323_) as usize);
    return v_r_1324_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(
    mut v_ref_1326_: *mut leanh::LeanObject,
    mut v_msgData_1327_: *mut leanh::LeanObject,
    mut v_severity_1328_: u8,
    mut v_isSilent_1329_: u8,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: u8 = 0;
    let mut v___y_1336_: u8 = 0;
    let mut v___y_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___y_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1371_: u8 = 0;
    let mut v___y_1372_: u8 = 0;
    let mut v___y_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: u8 = 0;
    let mut v___y_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut v___y_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1396_: u8 = 0;
    let mut v___y_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: u8 = 0;
    let mut v___y_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1400_: u8 = 0;
    let mut v___y_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1407_: u8 = 0;
    let mut v___y_1408_: u8 = 0;
    let mut v___y_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: u8 = 0;
    let mut v_ref_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___y_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v___y_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: u8 = 0;
    let mut v___y_1425_: u8 = 0;
    let mut v___y_1427_: u8 = 0;
    let mut v_fileName_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc_ref(v_msgData_1327_);
                    v___x_1443_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1327_);
                    v___y_1427_ = v___x_1443_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1343_ = lean_st_ref_take(v___y_1342_);
                v_currNamespace_1344_ = leanh::lean_ctor_get(v___y_1341_, 6);
                v_openDecls_1345_ = leanh::lean_ctor_get(v___y_1341_, 7);
                v_env_1346_ = leanh::lean_ctor_get(v___x_1343_, 0);
                v_nextMacroScope_1347_ = leanh::lean_ctor_get(v___x_1343_, 1);
                v_ngen_1348_ = leanh::lean_ctor_get(v___x_1343_, 2);
                v_auxDeclNGen_1349_ = leanh::lean_ctor_get(v___x_1343_, 3);
                v_traceState_1350_ = leanh::lean_ctor_get(v___x_1343_, 4);
                v_cache_1351_ = leanh::lean_ctor_get(v___x_1343_, 5);
                v_messages_1352_ = leanh::lean_ctor_get(v___x_1343_, 6);
                v_infoState_1353_ = leanh::lean_ctor_get(v___x_1343_, 7);
                v_snapshotTasks_1354_ = leanh::lean_ctor_get(v___x_1343_, 8);
                v_isSharedCheck_1368_ = (!leanh::lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1368_ == 0 {
                    v___x_1356_ = v___x_1343_;
                    v_isShared_1357_ = v_isSharedCheck_1368_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1354_);
                    leanh::lean_inc(v_infoState_1353_);
                    leanh::lean_inc(v_messages_1352_);
                    leanh::lean_inc(v_cache_1351_);
                    leanh::lean_inc(v_traceState_1350_);
                    leanh::lean_inc(v_auxDeclNGen_1349_);
                    leanh::lean_inc(v_ngen_1348_);
                    leanh::lean_inc(v_nextMacroScope_1347_);
                    leanh::lean_inc(v_env_1346_);
                    leanh::lean_dec(v___x_1343_);
                    v___x_1356_ = leanh::lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_1345_);
                leanh::lean_inc(v_currNamespace_1344_);
                v___x_1358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1358_, 0, v_currNamespace_1344_);
                leanh::lean_ctor_set(v___x_1358_, 1, v_openDecls_1345_);
                v___x_1359_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1359_, 0, v___x_1358_);
                leanh::lean_ctor_set(v___x_1359_, 1, v___y_1338_);
                leanh::lean_inc_ref(v___y_1334_);
                leanh::lean_inc_ref(v___y_1337_);
                v___x_1360_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_1360_, 0, v___y_1337_);
                leanh::lean_ctor_set(v___x_1360_, 1, v___y_1340_);
                leanh::lean_ctor_set(v___x_1360_, 2, v___y_1339_);
                leanh::lean_ctor_set(v___x_1360_, 3, v___y_1334_);
                leanh::lean_ctor_set(v___x_1360_, 4, v___x_1359_);
                leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_1335_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1336_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1360_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1329_,
                );
                v___x_1361_ = l_Lean_MessageLog_add(v___x_1360_, v_messages_1352_);
                if v_isShared_1357_ == 0 {
                    leanh::lean_ctor_set(v___x_1356_, 6, v___x_1361_);
                    v___x_1363_ = v___x_1356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_env_1346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_nextMacroScope_1347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_ngen_1348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_auxDeclNGen_1349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_traceState_1350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 5, v_cache_1351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 6, v___x_1361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 7, v_infoState_1353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 8, v_snapshotTasks_1354_);
                    v___x_1363_ = v_reuseFailAlloc_1367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1364_ = lean_st_ref_set(v___y_1342_, v___x_1363_);
                v___x_1365_ = leanh::lean_box(0);
                v___x_1366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1366_, 0, v___x_1365_);
                return v___x_1366_;
            }
            4 => {
                v___x_1378_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1327_,
                    );
                v___x_1379_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v___x_1378_, v___y_1330_, v___y_1331_);
                v_a_1380_ = leanh::lean_ctor_get(v___x_1379_, 0);
                v_isSharedCheck_1393_ = (!leanh::lean_is_exclusive(v___x_1379_)) as u8;
                if v_isSharedCheck_1393_ == 0 {
                    v___x_1382_ = v___x_1379_;
                    v_isShared_1383_ = v_isSharedCheck_1393_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1380_);
                    leanh::lean_dec(v___x_1379_);
                    v___x_1382_ = leanh::lean_box(0);
                    v_isShared_1383_ = v_isSharedCheck_1393_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_1375_, 2);
                v___x_1384_ = l_Lean_FileMap_toPosition(v___y_1375_, v___y_1376_);
                leanh::lean_dec(v___y_1376_);
                v___x_1385_ = l_Lean_FileMap_toPosition(v___y_1375_, v___y_1377_);
                leanh::lean_dec(v___y_1377_);
                v___x_1386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1386_, 0, v___x_1385_);
                v___x_1387_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___closed__0;
                if v___y_1372_ == 0 {
                    leanh::lean_del_object(v___x_1382_);
                    leanh::lean_dec_ref(v___y_1370_);
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
                    leanh::lean_inc(v_a_1380_);
                    v___x_1388_ = l_Lean_MessageData_hasTag(v___y_1370_, v_a_1380_);
                    if v___x_1388_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1386_, 1);
                        leanh::lean_dec_ref(v___x_1384_);
                        leanh::lean_dec(v_a_1380_);
                        v___x_1389_ = leanh::lean_box(0);
                        if v_isShared_1383_ == 0 {
                            leanh::lean_ctor_set(v___x_1382_, 0, v___x_1389_);
                            v___x_1391_ = v___x_1382_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1392_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
                            v___x_1391_ = v_reuseFailAlloc_1392_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1382_);
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
                leanh::lean_dec(v___y_1401_);
                if leanh::lean_obj_tag(v___x_1403_) == 0 {
                    leanh::lean_inc(v___y_1402_);
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
                    v_val_1404_ = leanh::lean_ctor_get(v___x_1403_, 0);
                    leanh::lean_inc(v_val_1404_);
                    leanh::lean_dec_ref_known(v___x_1403_, 1);
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
                if leanh::lean_obj_tag(v___x_1414_) == 0 {
                    v___x_1415_ = leanh::lean_unsigned_to_nat(0);
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
                    v_val_1416_ = leanh::lean_ctor_get(v___x_1414_, 0);
                    leanh::lean_inc(v_val_1416_);
                    leanh::lean_dec_ref_known(v___x_1414_, 1);
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
                    v_fileName_1428_ = leanh::lean_ctor_get(v___y_1330_, 0);
                    v_fileMap_1429_ = leanh::lean_ctor_get(v___y_1330_, 1);
                    v_options_1430_ = leanh::lean_ctor_get(v___y_1330_, 2);
                    v_ref_1431_ = leanh::lean_ctor_get(v___y_1330_, 5);
                    v_suppressElabErrors_1432_ = leanh::lean_ctor_get_uint8(
                        v___y_1330_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_1433_ = leanh::lean_box((v___y_1427_) as usize);
                    v___x_1434_ = leanh::lean_box((v_suppressElabErrors_1432_) as usize);
                    v___f_1435_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_1435_, 0, v___x_1433_);
                    leanh::lean_closure_set(v___f_1435_, 1, v___x_1434_);
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
                    leanh::lean_dec_ref(v_msgData_1327_);
                    v___x_1440_ = leanh::lean_box(0);
                    v___x_1441_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1441_, 0, v___x_1440_);
                    return v___x_1441_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9___boxed(
    mut v_ref_1444_: *mut leanh::LeanObject,
    mut v_msgData_1445_: *mut leanh::LeanObject,
    mut v_severity_1446_: *mut leanh::LeanObject,
    mut v_isSilent_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_1451_: u8 = 0;
    let mut v_isSilent_boxed_1452_: u8 = 0;
    let mut v_res_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1451_ = (leanh::lean_unbox(v_severity_1446_) as u8);
    v_isSilent_boxed_1452_ = (leanh::lean_unbox(v_isSilent_1447_) as u8);
    v_res_1453_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1444_, v_msgData_1445_, v_severity_boxed_1451_, v_isSilent_boxed_1452_, v___y_1448_, v___y_1449_);
    leanh::lean_dec(v___y_1449_);
    leanh::lean_dec_ref(v___y_1448_);
    leanh::lean_dec(v_ref_1444_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(
    mut v_msgData_1454_: *mut leanh::LeanObject,
    mut v_severity_1455_: u8,
    mut v_isSilent_1456_: u8,
    mut v___y_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1460_ = leanh::lean_ctor_get(v___y_1457_, 5);
    v___x_1461_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1460_, v_msgData_1454_, v_severity_1455_, v_isSilent_1456_, v___y_1457_, v___y_1458_);
    return v___x_1461_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12___boxed(
    mut v_msgData_1462_: *mut leanh::LeanObject,
    mut v_severity_1463_: *mut leanh::LeanObject,
    mut v_isSilent_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: *mut leanh::LeanObject,
    mut v___y_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_1468_: u8 = 0;
    let mut v_isSilent_boxed_1469_: u8 = 0;
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1468_ = (leanh::lean_unbox(v_severity_1463_) as u8);
    v_isSilent_boxed_1469_ = (leanh::lean_unbox(v_isSilent_1464_) as u8);
    v_res_1470_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(v_msgData_1462_, v_severity_boxed_1468_, v_isSilent_boxed_1469_, v___y_1465_, v___y_1466_);
    leanh::lean_dec(v___y_1466_);
    leanh::lean_dec_ref(v___y_1465_);
    return v_res_1470_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(
    mut v_msgData_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1475_ = 1;
    v___x_1476_ = 0;
    v___x_1477_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6_spec__12(v_msgData_1471_, v___x_1475_, v___x_1476_, v___y_1472_, v___y_1473_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6___boxed(
    mut v_msgData_1478_: *mut leanh::LeanObject,
    mut v___y_1479_: *mut leanh::LeanObject,
    mut v___y_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(v_msgData_1478_, v___y_1479_, v___y_1480_);
    leanh::lean_dec(v___y_1480_);
    leanh::lean_dec_ref(v___y_1479_);
    return v_res_1482_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v_isExporting_1484_: u8,
    mut v___x_1485_: *mut leanh::LeanObject,
    mut v_a_x3f_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_unused_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1488_ = lean_st_ref_take(v___y_1483_);
                v_env_1489_ = leanh::lean_ctor_get(v___x_1488_, 0);
                v_nextMacroScope_1490_ = leanh::lean_ctor_get(v___x_1488_, 1);
                v_ngen_1491_ = leanh::lean_ctor_get(v___x_1488_, 2);
                v_auxDeclNGen_1492_ = leanh::lean_ctor_get(v___x_1488_, 3);
                v_traceState_1493_ = leanh::lean_ctor_get(v___x_1488_, 4);
                v_messages_1494_ = leanh::lean_ctor_get(v___x_1488_, 6);
                v_infoState_1495_ = leanh::lean_ctor_get(v___x_1488_, 7);
                v_snapshotTasks_1496_ = leanh::lean_ctor_get(v___x_1488_, 8);
                v_isSharedCheck_1507_ = (!leanh::lean_is_exclusive(v___x_1488_)) as u8;
                if v_isSharedCheck_1507_ == 0 {
                    v_unused_1508_ = leanh::lean_ctor_get(v___x_1488_, 5);
                    leanh::lean_dec(v_unused_1508_);
                    v___x_1498_ = v___x_1488_;
                    v_isShared_1499_ = v_isSharedCheck_1507_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1496_);
                    leanh::lean_inc(v_infoState_1495_);
                    leanh::lean_inc(v_messages_1494_);
                    leanh::lean_inc(v_traceState_1493_);
                    leanh::lean_inc(v_auxDeclNGen_1492_);
                    leanh::lean_inc(v_ngen_1491_);
                    leanh::lean_inc(v_nextMacroScope_1490_);
                    leanh::lean_inc(v_env_1489_);
                    leanh::lean_dec(v___x_1488_);
                    v___x_1498_ = leanh::lean_box(0);
                    v_isShared_1499_ = v_isSharedCheck_1507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1500_ = l_Lean_Environment_setExporting(v_env_1489_, v_isExporting_1484_);
                if v_isShared_1499_ == 0 {
                    leanh::lean_ctor_set(v___x_1498_, 5, v___x_1485_);
                    leanh::lean_ctor_set(v___x_1498_, 0, v___x_1500_);
                    v___x_1502_ = v___x_1498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_nextMacroScope_1490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_ngen_1491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_auxDeclNGen_1492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_traceState_1493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 5, v___x_1485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_messages_1494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_infoState_1495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_snapshotTasks_1496_);
                    v___x_1502_ = v_reuseFailAlloc_1506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1503_ = lean_st_ref_set(v___y_1483_, v___x_1502_);
                v___x_1504_ = leanh::lean_box(0);
                v___x_1505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                return v___x_1505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v_isExporting_1510_: *mut leanh::LeanObject,
    mut v___x_1511_: *mut leanh::LeanObject,
    mut v_a_x3f_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_1514_: u8 = 0;
    let mut v_res_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1514_ = (leanh::lean_unbox(v_isExporting_1510_) as u8);
    v_res_1515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1509_, v_isExporting_boxed_1514_, v___x_1511_, v_a_x3f_1512_);
    leanh::lean_dec(v_a_x3f_1512_);
    leanh::lean_dec(v___y_1509_);
    return v_res_1515_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1516_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0);
    v___x_1518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
    v___x_1520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
    leanh::lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_1521_: *mut leanh::LeanObject,
    mut v_isExporting_1522_: u8,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1528_: u8 = 0;
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_unused_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1526_ = lean_st_ref_get(v___y_1524_);
                v_env_1527_ = leanh::lean_ctor_get(v___x_1526_, 0);
                leanh::lean_inc_ref(v_env_1527_);
                leanh::lean_dec(v___x_1526_);
                v_isExporting_1528_ = leanh::lean_ctor_get_uint8(
                    v_env_1527_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_1527_);
                v___x_1529_ = lean_st_ref_take(v___y_1524_);
                v_env_1530_ = leanh::lean_ctor_get(v___x_1529_, 0);
                v_nextMacroScope_1531_ = leanh::lean_ctor_get(v___x_1529_, 1);
                v_ngen_1532_ = leanh::lean_ctor_get(v___x_1529_, 2);
                v_auxDeclNGen_1533_ = leanh::lean_ctor_get(v___x_1529_, 3);
                v_traceState_1534_ = leanh::lean_ctor_get(v___x_1529_, 4);
                v_messages_1535_ = leanh::lean_ctor_get(v___x_1529_, 6);
                v_infoState_1536_ = leanh::lean_ctor_get(v___x_1529_, 7);
                v_snapshotTasks_1537_ = leanh::lean_ctor_get(v___x_1529_, 8);
                v_isSharedCheck_1576_ = (!leanh::lean_is_exclusive(v___x_1529_)) as u8;
                if v_isSharedCheck_1576_ == 0 {
                    v_unused_1577_ = leanh::lean_ctor_get(v___x_1529_, 5);
                    leanh::lean_dec(v_unused_1577_);
                    v___x_1539_ = v___x_1529_;
                    v_isShared_1540_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1537_);
                    leanh::lean_inc(v_infoState_1536_);
                    leanh::lean_inc(v_messages_1535_);
                    leanh::lean_inc(v_traceState_1534_);
                    leanh::lean_inc(v_auxDeclNGen_1533_);
                    leanh::lean_inc(v_ngen_1532_);
                    leanh::lean_inc(v_nextMacroScope_1531_);
                    leanh::lean_inc(v_env_1530_);
                    leanh::lean_dec(v___x_1529_);
                    v___x_1539_ = leanh::lean_box(0);
                    v_isShared_1540_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1541_ = l_Lean_Environment_setExporting(v_env_1530_, v_isExporting_1522_);
                v___x_1542_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2);
                if v_isShared_1540_ == 0 {
                    leanh::lean_ctor_set(v___x_1539_, 5, v___x_1542_);
                    leanh::lean_ctor_set(v___x_1539_, 0, v___x_1541_);
                    v___x_1544_ = v___x_1539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_messages_1535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_infoState_1536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_snapshotTasks_1537_);
                    v___x_1544_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1545_ = lean_st_ref_set(v___y_1524_, v___x_1544_);
                leanh::lean_inc(v___y_1524_);
                leanh::lean_inc_ref(v___y_1523_);
                v_r_1546_ = leanh::lean_apply_3(
                    v_x_1521_,
                    v___y_1523_,
                    v___y_1524_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1546_) == 0 {
                    v_a_1547_ = leanh::lean_ctor_get(v_r_1546_, 0);
                    v_isSharedCheck_1563_ = (!leanh::lean_is_exclusive(v_r_1546_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v___x_1549_ = v_r_1546_;
                        v_isShared_1550_ = v_isSharedCheck_1563_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1547_);
                        leanh::lean_dec(v_r_1546_);
                        v___x_1549_ = leanh::lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1563_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1564_ = leanh::lean_ctor_get(v_r_1546_, 0);
                    leanh::lean_inc(v_a_1564_);
                    leanh::lean_dec_ref_known(v_r_1546_, 1);
                    v___x_1565_ = leanh::lean_box(0);
                    v___x_1566_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1524_, v_isExporting_1528_, v___x_1542_, v___x_1565_);
                    v_isSharedCheck_1573_ = (!leanh::lean_is_exclusive(v___x_1566_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v_unused_1574_ = leanh::lean_ctor_get(v___x_1566_, 0);
                        leanh::lean_dec(v_unused_1574_);
                        v___x_1568_ = v___x_1566_;
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1566_);
                        v___x_1568_ = leanh::lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_1547_);
                if v_isShared_1550_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1549_, 1);
                    v___x_1552_ = v___x_1549_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1547_);
                    v___x_1552_ = v_reuseFailAlloc_1562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(v___y_1524_, v_isExporting_1528_, v___x_1542_, v___x_1552_);
                leanh::lean_dec_ref(v___x_1552_);
                v_isSharedCheck_1560_ = (!leanh::lean_is_exclusive(v___x_1553_)) as u8;
                if v_isSharedCheck_1560_ == 0 {
                    v_unused_1561_ = leanh::lean_ctor_get(v___x_1553_, 0);
                    leanh::lean_dec(v_unused_1561_);
                    v___x_1555_ = v___x_1553_;
                    v_isShared_1556_ = v_isSharedCheck_1560_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1553_);
                    v___x_1555_ = leanh::lean_box(0);
                    v_isShared_1556_ = v_isSharedCheck_1560_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1556_ == 0 {
                    leanh::lean_ctor_set(v___x_1555_, 0, v_a_1547_);
                    v___x_1558_ = v___x_1555_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1547_);
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
                    leanh::lean_ctor_set_tag(v___x_1568_, 1);
                    leanh::lean_ctor_set(v___x_1568_, 0, v_a_1564_);
                    v___x_1571_ = v___x_1568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1564_);
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
    mut v_x_1578_: *mut leanh::LeanObject,
    mut v_isExporting_1579_: *mut leanh::LeanObject,
    mut v___y_1580_: *mut leanh::LeanObject,
    mut v___y_1581_: *mut leanh::LeanObject,
    mut v___y_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1583_ = (leanh::lean_unbox(v_isExporting_1579_) as u8);
    v_res_1584_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_1578_, v_isExporting_boxed_1583_, v___y_1580_, v___y_1581_);
    leanh::lean_dec(v___y_1581_);
    leanh::lean_dec_ref(v___y_1580_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_1585_: *mut leanh::LeanObject,
    mut v_when_1586_: u8,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_1586_ == 0 {
        let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_1588_);
        leanh::lean_inc_ref(v___y_1587_);
        v___x_1590_ = leanh::lean_apply_3(
            v_x_1585_,
            v___y_1587_,
            v___y_1588_,
            leanh::lean_box(0),
        );
        return v___x_1590_;
    } else {
        let mut v___x_1591_: u8 = 0;
        let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1591_ = 0;
        v___x_1592_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_1585_, v___x_1591_, v___y_1587_, v___y_1588_);
        return v___x_1592_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_1593_: *mut leanh::LeanObject,
    mut v_when_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_1598_ = (leanh::lean_unbox(v_when_1594_) as u8);
    v_res_1599_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v_x_1593_, v_when_boxed_1598_, v___y_1595_, v___y_1596_);
    leanh::lean_dec(v___y_1596_);
    leanh::lean_dec_ref(v___y_1595_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(
    mut v_ref_1600_: *mut leanh::LeanObject,
    mut v_msgData_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = 1;
    v___x_1606_ = 0;
    v___x_1607_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4_spec__9(v_ref_1600_, v_msgData_1601_, v___x_1605_, v___x_1606_, v___y_1602_, v___y_1603_);
    return v___x_1607_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4___boxed(
    mut v_ref_1608_: *mut leanh::LeanObject,
    mut v_msgData_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(v_ref_1608_, v_msgData_1609_, v___y_1610_, v___y_1611_);
    leanh::lean_dec(v___y_1611_);
    leanh::lean_dec_ref(v___y_1610_);
    leanh::lean_dec(v_ref_1608_);
    return v_res_1613_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1618_ = leanh::lean_ctor_get(v___y_1615_, 5);
                v___x_1619_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0(v_msg_1614_, v___y_1615_, v___y_1616_);
                v_a_1620_ = leanh::lean_ctor_get(v___x_1619_, 0);
                v_isSharedCheck_1628_ = (!leanh::lean_is_exclusive(v___x_1619_)) as u8;
                if v_isSharedCheck_1628_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    v_isShared_1623_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1620_);
                    leanh::lean_dec(v___x_1619_);
                    v___x_1622_ = leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1618_);
                v___x_1624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1624_, 0, v_ref_1618_);
                leanh::lean_ctor_set(v___x_1624_, 1, v_a_1620_);
                if v_isShared_1623_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1622_, 1);
                    leanh::lean_ctor_set(v___x_1622_, 0, v___x_1624_);
                    v___x_1626_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
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
    mut v_msg_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_1629_, v___y_1630_, v___y_1631_);
    leanh::lean_dec(v___y_1631_);
    leanh::lean_dec_ref(v___y_1630_);
    return v_res_1633_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__0;
    v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__2;
    v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
    return v___x_1639_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__4;
    v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(
    mut v_name_1646_: *mut leanh::LeanObject,
    mut v_kind_1647_: u8,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1651_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__1);
                v___x_1652_ = l_Lean_MessageData_ofName(v_name_1646_);
                v___x_1653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1653_, 0, v___x_1651_);
                leanh::lean_ctor_set(v___x_1653_, 1, v___x_1652_);
                v___x_1654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__3);
                v___x_1655_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1655_, 0, v___x_1653_);
                leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
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
                leanh::lean_inc_ref(v___y_1657_);
                v___x_1658_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1658_, 0, v___y_1657_);
                v___x_1659_ = l_Lean_MessageData_ofFormat(v___x_1658_);
                v___x_1660_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1660_, 0, v___x_1655_);
                leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                v___x_1661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5);
                v___x_1662_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1662_, 0, v___x_1660_);
                leanh::lean_ctor_set(v___x_1662_, 1, v___x_1661_);
                v___x_1663_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_1662_, v___y_1648_, v___y_1649_);
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___boxed(
    mut v_name_1667_: *mut leanh::LeanObject,
    mut v_kind_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1672_: u8 = 0;
    let mut v_res_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1672_ = (leanh::lean_unbox(v_kind_1668_) as u8);
    v_res_1673_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v_name_1667_, v_kind_boxed_1672_, v___y_1669_, v___y_1670_);
    leanh::lean_dec(v___y_1670_);
    leanh::lean_dec_ref(v___y_1669_);
    return v_res_1673_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(
    mut v_ref_1674_: *mut leanh::LeanObject,
    mut v_msg_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1691_: u8 = 0;
    let mut v_cancelTk_x3f_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1693_: u8 = 0;
    let mut v_inheritedTraceOptions_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1679_ = leanh::lean_ctor_get(v___y_1676_, 0);
    v_fileMap_1680_ = leanh::lean_ctor_get(v___y_1676_, 1);
    v_options_1681_ = leanh::lean_ctor_get(v___y_1676_, 2);
    v_currRecDepth_1682_ = leanh::lean_ctor_get(v___y_1676_, 3);
    v_maxRecDepth_1683_ = leanh::lean_ctor_get(v___y_1676_, 4);
    v_ref_1684_ = leanh::lean_ctor_get(v___y_1676_, 5);
    v_currNamespace_1685_ = leanh::lean_ctor_get(v___y_1676_, 6);
    v_openDecls_1686_ = leanh::lean_ctor_get(v___y_1676_, 7);
    v_initHeartbeats_1687_ = leanh::lean_ctor_get(v___y_1676_, 8);
    v_maxHeartbeats_1688_ = leanh::lean_ctor_get(v___y_1676_, 9);
    v_quotContext_1689_ = leanh::lean_ctor_get(v___y_1676_, 10);
    v_currMacroScope_1690_ = leanh::lean_ctor_get(v___y_1676_, 11);
    v_diag_1691_ = leanh::lean_ctor_get_uint8(
        v___y_1676_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1692_ = leanh::lean_ctor_get(v___y_1676_, 12);
    v_suppressElabErrors_1693_ = leanh::lean_ctor_get_uint8(
        v___y_1676_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1694_ = leanh::lean_ctor_get(v___y_1676_, 13);
    v_ref_1695_ = l_Lean_replaceRef(v_ref_1674_, v_ref_1684_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1694_);
    leanh::lean_inc(v_cancelTk_x3f_1692_);
    leanh::lean_inc(v_currMacroScope_1690_);
    leanh::lean_inc(v_quotContext_1689_);
    leanh::lean_inc(v_maxHeartbeats_1688_);
    leanh::lean_inc(v_initHeartbeats_1687_);
    leanh::lean_inc(v_openDecls_1686_);
    leanh::lean_inc(v_currNamespace_1685_);
    leanh::lean_inc(v_maxRecDepth_1683_);
    leanh::lean_inc(v_currRecDepth_1682_);
    leanh::lean_inc_ref(v_options_1681_);
    leanh::lean_inc_ref(v_fileMap_1680_);
    leanh::lean_inc_ref(v_fileName_1679_);
    v___x_1696_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1696_, 0, v_fileName_1679_);
    leanh::lean_ctor_set(v___x_1696_, 1, v_fileMap_1680_);
    leanh::lean_ctor_set(v___x_1696_, 2, v_options_1681_);
    leanh::lean_ctor_set(v___x_1696_, 3, v_currRecDepth_1682_);
    leanh::lean_ctor_set(v___x_1696_, 4, v_maxRecDepth_1683_);
    leanh::lean_ctor_set(v___x_1696_, 5, v_ref_1695_);
    leanh::lean_ctor_set(v___x_1696_, 6, v_currNamespace_1685_);
    leanh::lean_ctor_set(v___x_1696_, 7, v_openDecls_1686_);
    leanh::lean_ctor_set(v___x_1696_, 8, v_initHeartbeats_1687_);
    leanh::lean_ctor_set(v___x_1696_, 9, v_maxHeartbeats_1688_);
    leanh::lean_ctor_set(v___x_1696_, 10, v_quotContext_1689_);
    leanh::lean_ctor_set(v___x_1696_, 11, v_currMacroScope_1690_);
    leanh::lean_ctor_set(v___x_1696_, 12, v_cancelTk_x3f_1692_);
    leanh::lean_ctor_set(v___x_1696_, 13, v_inheritedTraceOptions_1694_);
    leanh::lean_ctor_set_uint8(
        v___x_1696_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1691_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1696_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1693_,
    );
    v___x_1697_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_1675_, v___x_1696_, v___y_1677_);
    leanh::lean_dec_ref_known(v___x_1696_, 14);
    return v___x_1697_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg___boxed(
    mut v_ref_1698_: *mut leanh::LeanObject,
    mut v_msg_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_1698_, v_msg_1699_, v___y_1700_, v___y_1701_);
    leanh::lean_dec(v___y_1701_);
    leanh::lean_dec_ref(v___y_1700_);
    leanh::lean_dec(v_ref_1698_);
    return v_res_1703_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__0;
    v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__2;
    v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__4;
    v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(
    mut v_msg_1725_: *mut leanh::LeanObject,
    mut v_declHint_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v_isExporting_1732_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1729_ = lean_st_ref_get(v___y_1727_);
                v_env_1730_ = leanh::lean_ctor_get(v___x_1729_, 0);
                leanh::lean_inc_ref(v_env_1730_);
                leanh::lean_dec(v___x_1729_);
                v___x_1731_ = l_Lean_Name_isAnonymous(v_declHint_1726_);
                if v___x_1731_ == 0 {
                    v_isExporting_1732_ = leanh::lean_ctor_get_uint8(
                        v_env_1730_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1732_ == 0 {
                        leanh::lean_dec_ref(v_env_1730_);
                        leanh::lean_dec(v_declHint_1726_);
                        v___x_1733_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1733_, 0, v_msg_1725_);
                        return v___x_1733_;
                    } else {
                        leanh::lean_inc_ref(v_env_1730_);
                        v___x_1734_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1731_);
                        leanh::lean_inc(v_declHint_1726_);
                        leanh::lean_inc_ref(v___x_1734_);
                        v___x_1735_ = l_Lean_Environment_contains(
                            v___x_1734_,
                            v_declHint_1726_,
                            v_isExporting_1732_,
                        );
                        if v___x_1735_ == 0 {
                            leanh::lean_dec_ref(v___x_1734_);
                            leanh::lean_dec_ref(v_env_1730_);
                            leanh::lean_dec(v_declHint_1726_);
                            v___x_1736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1736_, 0, v_msg_1725_);
                            return v___x_1736_;
                        } else {
                            v___x_1737_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__2);
                            v___x_1738_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0_spec__0___closed__5);
                            v___x_1739_ = l_Lean_Options_empty;
                            v___x_1740_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1740_, 0, v___x_1734_);
                            leanh::lean_ctor_set(v___x_1740_, 1, v___x_1737_);
                            leanh::lean_ctor_set(v___x_1740_, 2, v___x_1738_);
                            leanh::lean_ctor_set(v___x_1740_, 3, v___x_1739_);
                            leanh::lean_inc(v_declHint_1726_);
                            v___x_1741_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1726_, v___x_1731_);
                            v_c_1742_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1742_, 0, v___x_1740_);
                            leanh::lean_ctor_set(v_c_1742_, 1, v___x_1741_);
                            v___x_1743_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1730_,
                                v_declHint_1726_,
                            );
                            if leanh::lean_obj_tag(v___x_1743_) == 0 {
                                leanh::lean_dec_ref(v_env_1730_);
                                leanh::lean_dec(v_declHint_1726_);
                                v___x_1744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1);
                                v___x_1745_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
                                leanh::lean_ctor_set(v___x_1745_, 1, v_c_1742_);
                                v___x_1746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__3);
                                v___x_1747_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                                leanh::lean_ctor_set(v___x_1747_, 1, v___x_1746_);
                                v___x_1748_ = l_Lean_MessageData_note(v___x_1747_);
                                v___x_1749_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1749_, 0, v_msg_1725_);
                                leanh::lean_ctor_set(v___x_1749_, 1, v___x_1748_);
                                v___x_1750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1750_, 0, v___x_1749_);
                                return v___x_1750_;
                            } else {
                                v_val_1751_ = leanh::lean_ctor_get(v___x_1743_, 0);
                                v_isSharedCheck_1786_ =
                                    (!leanh::lean_is_exclusive(v___x_1743_)) as u8;
                                if v_isSharedCheck_1786_ == 0 {
                                    v___x_1753_ = v___x_1743_;
                                    v_isShared_1754_ = v_isSharedCheck_1786_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1751_);
                                    leanh::lean_dec(v___x_1743_);
                                    v___x_1753_ = leanh::lean_box(0);
                                    v_isShared_1754_ = v_isSharedCheck_1786_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1730_);
                    leanh::lean_dec(v_declHint_1726_);
                    v___x_1787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1787_, 0, v_msg_1725_);
                    return v___x_1787_;
                }
            }
            1 => {
                v___x_1755_ = leanh::lean_box(0);
                v___x_1756_ = l_Lean_Environment_header(v_env_1730_);
                leanh::lean_dec_ref(v_env_1730_);
                v___x_1757_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1756_);
                v_mod_1758_ = lean_array_get(v___x_1755_, v___x_1757_, v_val_1751_);
                leanh::lean_dec(v_val_1751_);
                leanh::lean_dec_ref(v___x_1757_);
                v___x_1759_ = l_Lean_isPrivateName(v_declHint_1726_);
                leanh::lean_dec(v_declHint_1726_);
                if v___x_1759_ == 0 {
                    v___x_1760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__5);
                    v___x_1761_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
                    leanh::lean_ctor_set(v___x_1761_, 1, v_c_1742_);
                    v___x_1762_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_1763_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1763_, 0, v___x_1761_);
                    leanh::lean_ctor_set(v___x_1763_, 1, v___x_1762_);
                    v___x_1764_ = l_Lean_MessageData_ofName(v_mod_1758_);
                    v___x_1765_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
                    leanh::lean_ctor_set(v___x_1765_, 1, v___x_1764_);
                    v___x_1766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__9);
                    v___x_1767_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1767_, 0, v___x_1765_);
                    leanh::lean_ctor_set(v___x_1767_, 1, v___x_1766_);
                    v___x_1768_ = l_Lean_MessageData_note(v___x_1767_);
                    v___x_1769_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1769_, 0, v_msg_1725_);
                    leanh::lean_ctor_set(v___x_1769_, 1, v___x_1768_);
                    if v_isShared_1754_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1753_, 0);
                        leanh::lean_ctor_set(v___x_1753_, 0, v___x_1769_);
                        v___x_1771_ = v___x_1753_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                        v___x_1771_ = v_reuseFailAlloc_1772_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1773_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__1);
                    v___x_1774_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1774_, 0, v___x_1773_);
                    leanh::lean_ctor_set(v___x_1774_, 1, v_c_1742_);
                    v___x_1775_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_1776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1776_, 0, v___x_1774_);
                    leanh::lean_ctor_set(v___x_1776_, 1, v___x_1775_);
                    v___x_1777_ = l_Lean_MessageData_ofName(v_mod_1758_);
                    v___x_1778_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1776_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v___x_1777_);
                    v___x_1779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_1780_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1780_, 0, v___x_1778_);
                    leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
                    v___x_1781_ = l_Lean_MessageData_note(v___x_1780_);
                    v___x_1782_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1782_, 0, v_msg_1725_);
                    leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
                    if v_isShared_1754_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1753_, 0);
                        leanh::lean_ctor_set(v___x_1753_, 0, v___x_1782_);
                        v___x_1784_ = v___x_1753_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
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
    mut v_msg_1788_: *mut leanh::LeanObject,
    mut v_declHint_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_1788_, v_declHint_1789_, v___y_1790_);
    leanh::lean_dec(v___y_1790_);
    return v_res_1792_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(
    mut v_msg_1793_: *mut leanh::LeanObject,
    mut v_declHint_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1798_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_1793_, v_declHint_1794_, v___y_1796_);
                v_a_1799_ = leanh::lean_ctor_get(v___x_1798_, 0);
                v_isSharedCheck_1808_ = (!leanh::lean_is_exclusive(v___x_1798_)) as u8;
                if v_isSharedCheck_1808_ == 0 {
                    v___x_1801_ = v___x_1798_;
                    v_isShared_1802_ = v_isSharedCheck_1808_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1799_);
                    leanh::lean_dec(v___x_1798_);
                    v___x_1801_ = leanh::lean_box(0);
                    v_isShared_1802_ = v_isSharedCheck_1808_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1803_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1804_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                leanh::lean_ctor_set(v___x_1804_, 1, v_a_1799_);
                if v_isShared_1802_ == 0 {
                    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1804_);
                    v___x_1806_ = v___x_1801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
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
    mut v_msg_1809_: *mut leanh::LeanObject,
    mut v_declHint_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(v_msg_1809_, v_declHint_1810_, v___y_1811_, v___y_1812_);
    leanh::lean_dec(v___y_1812_);
    leanh::lean_dec_ref(v___y_1811_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(
    mut v_ref_1815_: *mut leanh::LeanObject,
    mut v_msg_1816_: *mut leanh::LeanObject,
    mut v_declHint_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17(v_msg_1816_, v_declHint_1817_, v___y_1818_, v___y_1819_);
    v_a_1822_ = leanh::lean_ctor_get(v___x_1821_, 0);
    leanh::lean_inc(v_a_1822_);
    leanh::lean_dec_ref(v___x_1821_);
    v___x_1823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_1815_, v_a_1822_, v___y_1818_, v___y_1819_);
    return v___x_1823_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg___boxed(
    mut v_ref_1824_: *mut leanh::LeanObject,
    mut v_msg_1825_: *mut leanh::LeanObject,
    mut v_declHint_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_1824_, v_msg_1825_, v_declHint_1826_, v___y_1827_, v___y_1828_);
    leanh::lean_dec(v___y_1828_);
    leanh::lean_dec_ref(v___y_1827_);
    leanh::lean_dec(v_ref_1824_);
    return v_res_1830_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__0;
    v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(
    mut v_ref_1834_: *mut leanh::LeanObject,
    mut v_constName_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___closed__1);
    v___x_1840_ = 0;
    leanh::lean_inc(v_constName_1835_);
    v___x_1841_ = l_Lean_MessageData_ofConstName(v_constName_1835_, v___x_1840_);
    v___x_1842_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1842_, 0, v___x_1839_);
    leanh::lean_ctor_set(v___x_1842_, 1, v___x_1841_);
    v___x_1843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg___closed__5);
    v___x_1844_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1844_, 0, v___x_1842_);
    leanh::lean_ctor_set(v___x_1844_, 1, v___x_1843_);
    v___x_1845_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_1834_, v___x_1844_, v_constName_1835_, v___y_1836_, v___y_1837_);
    return v___x_1845_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg___boxed(
    mut v_ref_1846_: *mut leanh::LeanObject,
    mut v_constName_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_1846_, v_constName_1847_, v___y_1848_, v___y_1849_);
    leanh::lean_dec(v___y_1849_);
    leanh::lean_dec_ref(v___y_1848_);
    leanh::lean_dec(v_ref_1846_);
    return v_res_1851_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(
    mut v_constName_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1856_ = leanh::lean_ctor_get(v___y_1853_, 5);
    v___x_1857_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_1856_, v_constName_1852_, v___y_1853_, v___y_1854_);
    return v___x_1857_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg___boxed(
    mut v_constName_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_1858_, v___y_1859_, v___y_1860_);
    leanh::lean_dec(v___y_1860_);
    leanh::lean_dec_ref(v___y_1859_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(
    mut v_constName_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1867_ = lean_st_ref_get(v___y_1865_);
                v_env_1868_ = leanh::lean_ctor_get(v___x_1867_, 0);
                leanh::lean_inc_ref(v_env_1868_);
                leanh::lean_dec(v___x_1867_);
                v___x_1869_ = 0;
                leanh::lean_inc(v_constName_1863_);
                v___x_1870_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_1868_,
                    v_constName_1863_,
                    v___x_1869_,
                );
                if leanh::lean_obj_tag(v___x_1870_) == 0 {
                    v___x_1871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_1863_, v___y_1864_, v___y_1865_);
                    return v___x_1871_;
                } else {
                    leanh::lean_dec(v_constName_1863_);
                    v_val_1872_ = leanh::lean_ctor_get(v___x_1870_, 0);
                    v_isSharedCheck_1879_ = (!leanh::lean_is_exclusive(v___x_1870_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1874_ = v___x_1870_;
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1872_);
                        leanh::lean_dec(v___x_1870_);
                        v___x_1874_ = leanh::lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1875_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1874_, 0);
                    v___x_1877_ = v___x_1874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_val_1872_);
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
    mut v_constName_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(v_constName_1880_, v___y_1881_, v___y_1882_);
    leanh::lean_dec(v___y_1882_);
    leanh::lean_dec_ref(v___y_1881_);
    return v_res_1884_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__7(
    mut v_a_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1885_) == 0 {
                    v___x_1887_ = l_List_reverse___redArg(v_a_1886_);
                    return v___x_1887_;
                } else {
                    v_head_1888_ = leanh::lean_ctor_get(v_a_1885_, 0);
                    v_tail_1889_ = leanh::lean_ctor_get(v_a_1885_, 1);
                    v_isSharedCheck_1898_ = (!leanh::lean_is_exclusive(v_a_1885_)) as u8;
                    if v_isSharedCheck_1898_ == 0 {
                        v___x_1891_ = v_a_1885_;
                        v_isShared_1892_ = v_isSharedCheck_1898_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1889_);
                        leanh::lean_inc(v_head_1888_);
                        leanh::lean_dec(v_a_1885_);
                        v___x_1891_ = leanh::lean_box(0);
                        v_isShared_1892_ = v_isSharedCheck_1898_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1893_ = l_Lean_mkLevelParam(v_head_1888_);
                if v_isShared_1892_ == 0 {
                    leanh::lean_ctor_set(v___x_1891_, 1, v_a_1886_);
                    leanh::lean_ctor_set(v___x_1891_, 0, v___x_1893_);
                    v___x_1895_ = v___x_1891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_a_1886_);
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
    mut v_constName_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v_levelParams_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_a_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_1899_);
                v___x_1903_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6(v_constName_1899_, v___y_1900_, v___y_1901_);
                if leanh::lean_obj_tag(v___x_1903_) == 0 {
                    v_a_1904_ = leanh::lean_ctor_get(v___x_1903_, 0);
                    v_isSharedCheck_1915_ = (!leanh::lean_is_exclusive(v___x_1903_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1906_ = v___x_1903_;
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1904_);
                        leanh::lean_dec(v___x_1903_);
                        v___x_1906_ = leanh::lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_constName_1899_);
                    v_a_1916_ = leanh::lean_ctor_get(v___x_1903_, 0);
                    v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v___x_1903_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1903_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1916_);
                        leanh::lean_dec(v___x_1903_);
                        v___x_1918_ = leanh::lean_box(0);
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_1908_ = leanh::lean_ctor_get(v_a_1904_, 1);
                leanh::lean_inc(v_levelParams_1908_);
                leanh::lean_dec(v_a_1904_);
                v___x_1909_ = leanh::lean_box(0);
                v___x_1910_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__7(v_levelParams_1908_, v___x_1909_);
                v___x_1911_ = l_Lean_mkConst(v_constName_1899_, v___x_1910_);
                if v_isShared_1907_ == 0 {
                    leanh::lean_ctor_set(v___x_1906_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
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
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
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
    mut v_constName_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v_constName_1924_, v___y_1925_, v___y_1926_);
    leanh::lean_dec(v___y_1926_);
    leanh::lean_dec_ref(v___y_1925_);
    return v_res_1928_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(
    mut v_x_1929_: *mut leanh::LeanObject,
    mut v_x_1930_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1929_) == 0 {
        if leanh::lean_obj_tag(v_x_1930_) == 0 {
            let mut v___x_1931_: u8 = 0;
            v___x_1931_ = 1;
            return v___x_1931_;
        } else {
            let mut v___x_1932_: u8 = 0;
            v___x_1932_ = 0;
            return v___x_1932_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1930_) == 0 {
            let mut v___x_1933_: u8 = 0;
            v___x_1933_ = 0;
            return v___x_1933_;
        } else {
            let mut v_val_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: u8 = 0;
            v_val_1934_ = leanh::lean_ctor_get(v_x_1929_, 0);
            v_val_1935_ = leanh::lean_ctor_get(v_x_1930_, 0);
            v___x_1936_ = lean_name_eq(v_val_1934_, v_val_1935_);
            return v___x_1936_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4___boxed(
    mut v_x_1937_: *mut leanh::LeanObject,
    mut v_x_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1939_: u8 = 0;
    let mut v_r_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1939_ = l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(v_x_1937_, v_x_1938_);
    leanh::lean_dec(v_x_1938_);
    leanh::lean_dec(v_x_1937_);
    v_r_1940_ = leanh::lean_box((v_res_1939_) as usize);
    return v_r_1940_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__0;
    v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__2;
    v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__4;
    v___x_1949_ = l_Lean_stringToMessageData(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__6;
    v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(
    mut v_declName_1953_: *mut leanh::LeanObject,
    mut v_target_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_unused_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1983_ = lean_st_ref_get(v___y_1956_);
                v_env_1984_ = leanh::lean_ctor_get(v___x_1983_, 0);
                leanh::lean_inc_ref(v_env_1984_);
                leanh::lean_dec(v___x_1983_);
                v___x_1985_ = leanh::lean_box(0);
                v___x_1999_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1984_, v_declName_1953_);
                leanh::lean_dec_ref(v_env_1984_);
                if leanh::lean_obj_tag(v___x_1999_) == 0 {
                    v___x_2000_ = lean_st_ref_get(v___y_1956_);
                    v_env_2001_ = leanh::lean_ctor_get(v___x_2000_, 0);
                    leanh::lean_inc_ref(v_env_2001_);
                    leanh::lean_dec(v___x_2000_);
                    v___x_2002_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
                    v_toEnvExtension_2003_ = leanh::lean_ctor_get(v___x_2002_, 0);
                    v_asyncMode_2004_ = leanh::lean_ctor_get(v_toEnvExtension_2003_, 2);
                    v___x_2005_ = 1;
                    leanh::lean_inc(v_declName_1953_);
                    v___x_2006_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                        v___x_1985_,
                        v___x_2002_,
                        v_env_2001_,
                        v_declName_1953_,
                        v_asyncMode_2004_,
                        v___x_2005_,
                    );
                    if leanh::lean_obj_tag(v___x_2006_) == 0 {
                        v___x_2007_ = lean_st_ref_get(v___y_1956_);
                        v_env_2008_ = leanh::lean_ctor_get(v___x_2007_, 0);
                        leanh::lean_inc_ref(v_env_2008_);
                        leanh::lean_dec(v___x_2007_);
                        v_____do__lift_1987_ = v_env_2008_;
                        v___y_1988_ = v___y_1955_;
                        v___y_1989_ = v___y_1956_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_2006_, 1);
                        leanh::lean_dec(v_target_1954_);
                        v___x_2009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3);
                        v___x_2010_ = 0;
                        v___x_2011_ = l_Lean_MessageData_ofConstName(v_declName_1953_, v___x_2010_);
                        v___x_2012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2012_, 0, v___x_2009_);
                        leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
                        v___x_2013_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__5);
                        v___x_2014_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                        leanh::lean_ctor_set(v___x_2014_, 1, v___x_2013_);
                        v___x_2015_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2014_, v___y_1955_, v___y_1956_);
                        return v___x_2015_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_1999_, 1);
                    leanh::lean_dec(v_target_1954_);
                    v___x_2016_ = 0;
                    v___x_2017_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__3);
                    v___x_2018_ = l_Lean_MessageData_ofConstName(v_declName_1953_, v___x_2016_);
                    v___x_2019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
                    leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                    v___x_2020_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__7);
                    v___x_2021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2021_, 0, v___x_2019_);
                    leanh::lean_ctor_set(v___x_2021_, 1, v___x_2020_);
                    v___x_2022_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2021_, v___y_1955_, v___y_1956_);
                    return v___x_2022_;
                }
            }
            1 => {
                v___x_1960_ = lean_st_ref_take(v___y_1959_);
                v_env_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
                v_nextMacroScope_1962_ = leanh::lean_ctor_get(v___x_1960_, 1);
                v_ngen_1963_ = leanh::lean_ctor_get(v___x_1960_, 2);
                v_auxDeclNGen_1964_ = leanh::lean_ctor_get(v___x_1960_, 3);
                v_traceState_1965_ = leanh::lean_ctor_get(v___x_1960_, 4);
                v_messages_1966_ = leanh::lean_ctor_get(v___x_1960_, 6);
                v_infoState_1967_ = leanh::lean_ctor_get(v___x_1960_, 7);
                v_snapshotTasks_1968_ = leanh::lean_ctor_get(v___x_1960_, 8);
                v_isSharedCheck_1981_ = (!leanh::lean_is_exclusive(v___x_1960_)) as u8;
                if v_isSharedCheck_1981_ == 0 {
                    v_unused_1982_ = leanh::lean_ctor_get(v___x_1960_, 5);
                    leanh::lean_dec(v_unused_1982_);
                    v___x_1970_ = v___x_1960_;
                    v_isShared_1971_ = v_isSharedCheck_1981_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1968_);
                    leanh::lean_inc(v_infoState_1967_);
                    leanh::lean_inc(v_messages_1966_);
                    leanh::lean_inc(v_traceState_1965_);
                    leanh::lean_inc(v_auxDeclNGen_1964_);
                    leanh::lean_inc(v_ngen_1963_);
                    leanh::lean_inc(v_nextMacroScope_1962_);
                    leanh::lean_inc(v_env_1961_);
                    leanh::lean_dec(v___x_1960_);
                    v___x_1970_ = leanh::lean_box(0);
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
                v___x_1974_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__2);
                if v_isShared_1971_ == 0 {
                    leanh::lean_ctor_set(v___x_1970_, 5, v___x_1974_);
                    leanh::lean_ctor_set(v___x_1970_, 0, v___x_1973_);
                    v___x_1976_ = v___x_1970_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_nextMacroScope_1962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_ngen_1963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_auxDeclNGen_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 4, v_traceState_1965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 5, v___x_1974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 6, v_messages_1966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 7, v_infoState_1967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 8, v_snapshotTasks_1968_);
                    v___x_1976_ = v_reuseFailAlloc_1980_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1977_ = lean_st_ref_set(v___y_1959_, v___x_1976_);
                v___x_1978_ = leanh::lean_box(0);
                v___x_1979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1979_, 0, v___x_1978_);
                return v___x_1979_;
            }
            4 => {
                v___x_1990_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
                v_toEnvExtension_1991_ = leanh::lean_ctor_get(v___x_1990_, 0);
                v_asyncMode_1992_ = leanh::lean_ctor_get(v_toEnvExtension_1991_, 2);
                v___x_1993_ = 1;
                leanh::lean_inc(v_target_1954_);
                v___x_1994_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_1985_,
                    v___x_1990_,
                    v_____do__lift_1987_,
                    v_target_1954_,
                    v_asyncMode_1992_,
                    v___x_1993_,
                );
                leanh::lean_inc(v_declName_1953_);
                v___x_1995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1995_, 0, v_declName_1953_);
                v___x_1996_ = l_Option_instBEq_beq___at___00Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2_spec__4(v___x_1994_, v___x_1995_);
                leanh::lean_dec_ref_known(v___x_1995_, 1);
                leanh::lean_dec(v___x_1994_);
                if v___x_1996_ == 0 {
                    v___y_1959_ = v___y_1989_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_target_1954_);
                    leanh::lean_dec(v_declName_1953_);
                    v___x_1997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1_once), _init_l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___closed__1);
                    v___x_1998_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_1997_, v___y_1988_, v___y_1989_);
                    return v___x_1998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2___boxed(
    mut v_declName_2023_: *mut leanh::LeanObject,
    mut v_target_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_declName_2023_, v_target_2024_, v___y_2025_, v___y_2026_);
    leanh::lean_dec(v___y_2026_);
    leanh::lean_dec_ref(v___y_2025_);
    return v_res_2028_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
    return v___x_2031_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
    return v___x_2034_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
    return v___x_2043_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(
    mut v___x_2047_: *mut leanh::LeanObject,
    mut v___x_2048_: *mut leanh::LeanObject,
    mut v___x_2049_: *mut leanh::LeanObject,
    mut v_decl_2050_: *mut leanh::LeanObject,
    mut v_stx_2051_: *mut leanh::LeanObject,
    mut v_kind_2052_: u8,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2057_: u8 = 0;
    let mut v___y_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v_ref_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v___y_2097_: u8 = 0;
    let mut v___y_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v___y_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2116_: u8 = 0;
    let mut v___y_2118_: u8 = 0;
    let mut v___y_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2135_: u8 = 0;
    let mut v_cancelTk_x3f_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2137_: u8 = 0;
    let mut v_inheritedTraceOptions_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2181_: u8 = 0;
    let mut v_a_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2189_: u8 = 0;
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2218_ = 0;
                v___x_2219_ = l_Lean_instBEqAttributeKind_beq(v_kind_2052_, v___x_2218_);
                if v___x_2219_ == 0 {
                    leanh::lean_dec(v_stx_2051_);
                    leanh::lean_dec(v_decl_2050_);
                    leanh::lean_dec_ref(v___x_2047_);
                    v___x_2220_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v___x_2049_, v_kind_2052_, v___y_2053_, v___y_2054_);
                    return v___x_2220_;
                } else {
                    state = 17;
                    continue;
                }
            }
            1 => {
                v___x_2062_ = lean_st_ref_get(v___y_2061_);
                v_env_2063_ = leanh::lean_ctor_get(v___x_2062_, 0);
                leanh::lean_inc_ref(v_env_2063_);
                leanh::lean_dec(v___x_2062_);
                leanh::lean_inc(v___y_2060_);
                v___x_2064_ =
                    l_Lean_findInternalDocString_x3f(v_env_2063_, v___y_2060_, v___y_2057_);
                if leanh::lean_obj_tag(v___x_2064_) == 0 {
                    v_a_2065_ = leanh::lean_ctor_get(v___x_2064_, 0);
                    leanh::lean_inc(v_a_2065_);
                    leanh::lean_dec_ref_known(v___x_2064_, 1);
                    if leanh::lean_obj_tag(v_a_2065_) == 0 {
                        if v___y_2057_ == 0 {
                            leanh::lean_dec(v___y_2059_);
                            v___x_2066_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                            leanh::lean_dec_ref(v___y_2058_);
                            return v___x_2066_;
                        } else {
                            leanh::lean_inc(v___y_2060_);
                            v___x_2067_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v___y_2060_, v___y_2058_, v___y_2061_);
                            if leanh::lean_obj_tag(v___x_2067_) == 0 {
                                v_a_2068_ = leanh::lean_ctor_get(v___x_2067_, 0);
                                leanh::lean_inc(v_a_2068_);
                                leanh::lean_dec_ref_known(v___x_2067_, 1);
                                v___x_2069_ = l_Lean_MessageData_ofExpr(v_a_2068_);
                                v___x_2070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                v___x_2071_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2071_, 0, v___x_2069_);
                                leanh::lean_ctor_set(v___x_2071_, 1, v___x_2070_);
                                v___x_2072_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__4(v___y_2059_, v___x_2071_, v___y_2058_, v___y_2061_);
                                leanh::lean_dec(v___y_2059_);
                                if leanh::lean_obj_tag(v___x_2072_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2072_, 1);
                                    v___x_2073_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                                    leanh::lean_dec_ref(v___y_2058_);
                                    return v___x_2073_;
                                } else {
                                    leanh::lean_dec(v___y_2060_);
                                    leanh::lean_dec_ref(v___y_2058_);
                                    leanh::lean_dec(v_decl_2050_);
                                    return v___x_2072_;
                                }
                            } else {
                                leanh::lean_dec(v___y_2060_);
                                leanh::lean_dec(v___y_2059_);
                                leanh::lean_dec_ref(v___y_2058_);
                                leanh::lean_dec(v_decl_2050_);
                                v_a_2074_ = leanh::lean_ctor_get(v___x_2067_, 0);
                                v_isSharedCheck_2081_ =
                                    (!leanh::lean_is_exclusive(v___x_2067_)) as u8;
                                if v_isSharedCheck_2081_ == 0 {
                                    v___x_2076_ = v___x_2067_;
                                    v_isShared_2077_ = v_isSharedCheck_2081_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2074_);
                                    leanh::lean_dec(v___x_2067_);
                                    v___x_2076_ = leanh::lean_box(0);
                                    v_isShared_2077_ = v_isSharedCheck_2081_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_2065_, 1);
                        leanh::lean_dec(v___y_2059_);
                        v___x_2082_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2060_, v___y_2058_, v___y_2061_);
                        leanh::lean_dec_ref(v___y_2058_);
                        return v___x_2082_;
                    }
                } else {
                    leanh::lean_dec(v___y_2060_);
                    leanh::lean_dec(v___y_2059_);
                    leanh::lean_dec(v_decl_2050_);
                    v_a_2083_ = leanh::lean_ctor_get(v___x_2064_, 0);
                    v_isSharedCheck_2095_ = (!leanh::lean_is_exclusive(v___x_2064_)) as u8;
                    if v_isSharedCheck_2095_ == 0 {
                        v___x_2085_ = v___x_2064_;
                        v_isShared_2086_ = v_isSharedCheck_2095_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2083_);
                        leanh::lean_dec(v___x_2064_);
                        v___x_2085_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2080_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
                    v___x_2079_ = v_reuseFailAlloc_2080_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2079_;
            }
            4 => {
                v_ref_2087_ = leanh::lean_ctor_get(v___y_2058_, 5);
                leanh::lean_inc(v_ref_2087_);
                leanh::lean_dec_ref(v___y_2058_);
                v___x_2088_ = lean_io_error_to_string(v_a_2083_);
                v___x_2089_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2089_, 0, v___x_2088_);
                v___x_2090_ = l_Lean_MessageData_ofFormat(v___x_2089_);
                v___x_2091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2091_, 0, v_ref_2087_);
                leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
                if v_isShared_2086_ == 0 {
                    leanh::lean_ctor_set(v___x_2085_, 0, v___x_2091_);
                    v___x_2093_ = v___x_2085_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
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
                leanh::lean_dec_ref(v___y_2099_);
                if v___x_2104_ == 0 {
                    leanh::lean_dec(v___y_2100_);
                    v___x_2105_ = l_Lean_addInheritedDocString___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__2(v_decl_2050_, v___y_2102_, v___y_2098_, v___y_2101_);
                    leanh::lean_dec_ref(v___y_2098_);
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
                v_env_2113_ = leanh::lean_ctor_get(v___x_2112_, 0);
                leanh::lean_inc_ref(v_env_2113_);
                leanh::lean_dec(v___x_2112_);
                v_options_2114_ = leanh::lean_ctor_get(v___y_2110_, 2);
                v___x_2115_ = l_Lean_Environment_header(v_env_2113_);
                leanh::lean_dec_ref(v_env_2113_);
                v_isModule_2116_ = leanh::lean_ctor_get_uint8(
                    v___x_2115_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_2115_);
                if v_isModule_2116_ == 0 {
                    if v___y_2107_ == 0 {
                        leanh::lean_inc_ref(v_options_2114_);
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
                    leanh::lean_inc_ref(v_options_2114_);
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
                v_fileName_2123_ = leanh::lean_ctor_get(v___y_2121_, 0);
                v_fileMap_2124_ = leanh::lean_ctor_get(v___y_2121_, 1);
                v_options_2125_ = leanh::lean_ctor_get(v___y_2121_, 2);
                v_currRecDepth_2126_ = leanh::lean_ctor_get(v___y_2121_, 3);
                v_maxRecDepth_2127_ = leanh::lean_ctor_get(v___y_2121_, 4);
                v_ref_2128_ = leanh::lean_ctor_get(v___y_2121_, 5);
                v_currNamespace_2129_ = leanh::lean_ctor_get(v___y_2121_, 6);
                v_openDecls_2130_ = leanh::lean_ctor_get(v___y_2121_, 7);
                v_initHeartbeats_2131_ = leanh::lean_ctor_get(v___y_2121_, 8);
                v_maxHeartbeats_2132_ = leanh::lean_ctor_get(v___y_2121_, 9);
                v_quotContext_2133_ = leanh::lean_ctor_get(v___y_2121_, 10);
                v_currMacroScope_2134_ = leanh::lean_ctor_get(v___y_2121_, 11);
                v_diag_2135_ = leanh::lean_ctor_get_uint8(
                    v___y_2121_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2136_ = leanh::lean_ctor_get(v___y_2121_, 12);
                v_suppressElabErrors_2137_ = leanh::lean_ctor_get_uint8(
                    v___y_2121_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2138_ = leanh::lean_ctor_get(v___y_2121_, 13);
                v_ref_2139_ = l_Lean_replaceRef(v___y_2119_, v_ref_2128_);
                leanh::lean_dec(v___y_2119_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2138_);
                leanh::lean_inc(v_cancelTk_x3f_2136_);
                leanh::lean_inc(v_currMacroScope_2134_);
                leanh::lean_inc(v_quotContext_2133_);
                leanh::lean_inc(v_maxHeartbeats_2132_);
                leanh::lean_inc(v_initHeartbeats_2131_);
                leanh::lean_inc(v_openDecls_2130_);
                leanh::lean_inc(v_currNamespace_2129_);
                leanh::lean_inc(v_ref_2139_);
                leanh::lean_inc(v_maxRecDepth_2127_);
                leanh::lean_inc(v_currRecDepth_2126_);
                leanh::lean_inc_ref(v_options_2125_);
                leanh::lean_inc_ref(v_fileMap_2124_);
                leanh::lean_inc_ref(v_fileName_2123_);
                v___x_2140_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2140_, 0, v_fileName_2123_);
                leanh::lean_ctor_set(v___x_2140_, 1, v_fileMap_2124_);
                leanh::lean_ctor_set(v___x_2140_, 2, v_options_2125_);
                leanh::lean_ctor_set(v___x_2140_, 3, v_currRecDepth_2126_);
                leanh::lean_ctor_set(v___x_2140_, 4, v_maxRecDepth_2127_);
                leanh::lean_ctor_set(v___x_2140_, 5, v_ref_2139_);
                leanh::lean_ctor_set(v___x_2140_, 6, v_currNamespace_2129_);
                leanh::lean_ctor_set(v___x_2140_, 7, v_openDecls_2130_);
                leanh::lean_ctor_set(v___x_2140_, 8, v_initHeartbeats_2131_);
                leanh::lean_ctor_set(v___x_2140_, 9, v_maxHeartbeats_2132_);
                leanh::lean_ctor_set(v___x_2140_, 10, v_quotContext_2133_);
                leanh::lean_ctor_set(v___x_2140_, 11, v_currMacroScope_2134_);
                leanh::lean_ctor_set(v___x_2140_, 12, v_cancelTk_x3f_2136_);
                leanh::lean_ctor_set(v___x_2140_, 13, v_inheritedTraceOptions_2138_);
                leanh::lean_ctor_set_uint8(
                    v___x_2140_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2135_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2140_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2137_,
                );
                if leanh::lean_obj_tag(v_id_x3f_2120_) == 1 {
                    v_val_2141_ = leanh::lean_ctor_get(v_id_x3f_2120_, 0);
                    v_isSharedCheck_2190_ =
                        (!leanh::lean_is_exclusive(v_id_x3f_2120_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2143_ = v_id_x3f_2120_;
                        v_isShared_2144_ = v_isSharedCheck_2190_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2141_);
                        leanh::lean_dec(v_id_x3f_2120_);
                        v___x_2143_ = leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2190_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_ref_2139_);
                    leanh::lean_dec(v_id_x3f_2120_);
                    leanh::lean_dec(v_decl_2050_);
                    v___x_2191_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                    v___x_2192_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2191_, v___x_2140_, v___y_2122_);
                    leanh::lean_dec_ref_known(v___x_2140_, 14);
                    return v___x_2192_;
                }
            }
            9 => {
                v___x_2145_ = leanh::lean_box(0);
                leanh::lean_inc(v_val_2141_);
                v___x_2146_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___x_2146_, 0, v_val_2141_);
                leanh::lean_closure_set(v___x_2146_, 1, v___x_2145_);
                v___x_2147_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v___x_2146_, v___y_2118_, v___x_2140_, v___y_2122_);
                if leanh::lean_obj_tag(v___x_2147_) == 0 {
                    v_a_2148_ = leanh::lean_ctor_get(v___x_2147_, 0);
                    leanh::lean_inc(v_a_2148_);
                    leanh::lean_dec_ref_known(v___x_2147_, 1);
                    v___x_2149_ = lean_st_ref_get(v___y_2122_);
                    v_env_2150_ = leanh::lean_ctor_get(v___x_2149_, 0);
                    leanh::lean_inc_ref(v_env_2150_);
                    leanh::lean_dec(v___x_2149_);
                    v___x_2151_ = 0;
                    leanh::lean_inc(v_decl_2050_);
                    v___x_2152_ =
                        l_Lean_findSimpleDocString_x3f(v_env_2150_, v_decl_2050_, v___x_2151_);
                    if leanh::lean_obj_tag(v___x_2152_) == 0 {
                        leanh::lean_del_object(v___x_2143_);
                        leanh::lean_dec(v_ref_2139_);
                        v_a_2153_ = leanh::lean_ctor_get(v___x_2152_, 0);
                        leanh::lean_inc(v_a_2153_);
                        leanh::lean_dec_ref_known(v___x_2152_, 1);
                        if leanh::lean_obj_tag(v_a_2153_) == 0 {
                            v___y_2107_ = v___y_2118_;
                            v___y_2108_ = v_val_2141_;
                            v___y_2109_ = v_a_2148_;
                            v___y_2110_ = v___x_2140_;
                            v___y_2111_ = v___y_2122_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_2153_, 1);
                            if v___y_2118_ == 0 {
                                v___y_2107_ = v___y_2118_;
                                v___y_2108_ = v_val_2141_;
                                v___y_2109_ = v_a_2148_;
                                v___y_2110_ = v___x_2140_;
                                v___y_2111_ = v___y_2122_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_decl_2050_);
                                v___x_2154_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3(v_decl_2050_, v___x_2140_, v___y_2122_);
                                if leanh::lean_obj_tag(v___x_2154_) == 0 {
                                    v_a_2155_ = leanh::lean_ctor_get(v___x_2154_, 0);
                                    leanh::lean_inc(v_a_2155_);
                                    leanh::lean_dec_ref_known(v___x_2154_, 1);
                                    v___x_2156_ = l_Lean_MessageData_ofExpr(v_a_2155_);
                                    v___x_2157_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                    v___x_2158_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2158_, 0, v___x_2156_);
                                    leanh::lean_ctor_set(v___x_2158_, 1, v___x_2157_);
                                    v___x_2159_ = l_Lean_logWarning___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__6(v___x_2158_, v___x_2140_, v___y_2122_);
                                    if leanh::lean_obj_tag(v___x_2159_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_2159_, 1);
                                        v___y_2107_ = v___y_2118_;
                                        v___y_2108_ = v_val_2141_;
                                        v___y_2109_ = v_a_2148_;
                                        v___y_2110_ = v___x_2140_;
                                        v___y_2111_ = v___y_2122_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_2148_);
                                        leanh::lean_dec(v_val_2141_);
                                        leanh::lean_dec_ref_known(v___x_2140_, 14);
                                        leanh::lean_dec(v_decl_2050_);
                                        return v___x_2159_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2148_);
                                    leanh::lean_dec(v_val_2141_);
                                    leanh::lean_dec_ref_known(v___x_2140_, 14);
                                    leanh::lean_dec(v_decl_2050_);
                                    v_a_2160_ = leanh::lean_ctor_get(v___x_2154_, 0);
                                    v_isSharedCheck_2167_ =
                                        (!leanh::lean_is_exclusive(v___x_2154_)) as u8;
                                    if v_isSharedCheck_2167_ == 0 {
                                        v___x_2162_ = v___x_2154_;
                                        v_isShared_2163_ = v_isSharedCheck_2167_;
                                        state = 10;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2160_);
                                        leanh::lean_dec(v___x_2154_);
                                        v___x_2162_ = leanh::lean_box(0);
                                        v_isShared_2163_ = v_isSharedCheck_2167_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2148_);
                        leanh::lean_dec(v_val_2141_);
                        leanh::lean_dec_ref_known(v___x_2140_, 14);
                        leanh::lean_dec(v_decl_2050_);
                        v_a_2168_ = leanh::lean_ctor_get(v___x_2152_, 0);
                        v_isSharedCheck_2181_ =
                            (!leanh::lean_is_exclusive(v___x_2152_)) as u8;
                        if v_isSharedCheck_2181_ == 0 {
                            v___x_2170_ = v___x_2152_;
                            v_isShared_2171_ = v_isSharedCheck_2181_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2168_);
                            leanh::lean_dec(v___x_2152_);
                            v___x_2170_ = leanh::lean_box(0);
                            v_isShared_2171_ = v_isSharedCheck_2181_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2143_);
                    leanh::lean_dec(v_val_2141_);
                    leanh::lean_dec_ref_known(v___x_2140_, 14);
                    leanh::lean_dec(v_ref_2139_);
                    leanh::lean_dec(v_decl_2050_);
                    v_a_2182_ = leanh::lean_ctor_get(v___x_2147_, 0);
                    v_isSharedCheck_2189_ = (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                    if v_isSharedCheck_2189_ == 0 {
                        v___x_2184_ = v___x_2147_;
                        v_isShared_2185_ = v_isSharedCheck_2189_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2182_);
                        leanh::lean_dec(v___x_2147_);
                        v___x_2184_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
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
                    leanh::lean_ctor_set_tag(v___x_2143_, 3);
                    leanh::lean_ctor_set(v___x_2143_, 0, v___x_2172_);
                    v___x_2174_ = v___x_2143_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2172_);
                    v___x_2174_ = v_reuseFailAlloc_2180_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2175_ = l_Lean_MessageData_ofFormat(v___x_2174_);
                v___x_2176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2176_, 0, v_ref_2139_);
                leanh::lean_ctor_set(v___x_2176_, 1, v___x_2175_);
                if v_isShared_2171_ == 0 {
                    leanh::lean_ctor_set(v___x_2170_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2170_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
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
                    v_reuseFailAlloc_2188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
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
                leanh::lean_inc(v_stx_2051_);
                v___x_2198_ = l_Lean_Syntax_isOfKind(v_stx_2051_, v___x_2197_);
                leanh::lean_dec(v___x_2197_);
                if v___x_2198_ == 0 {
                    leanh::lean_dec(v_stx_2051_);
                    leanh::lean_dec(v_decl_2050_);
                    leanh::lean_dec(v___x_2049_);
                    v___x_2199_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                    v___x_2200_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2199_, v___y_2053_, v___y_2054_);
                    return v___x_2200_;
                } else {
                    v___x_2201_ = l_Lean_Syntax_getArg(v_stx_2051_, v___x_2048_);
                    v___x_2202_ = l_Lean_Syntax_matchesIdent(v___x_2201_, v___x_2049_);
                    if v___x_2202_ == 0 {
                        leanh::lean_dec(v___x_2201_);
                        leanh::lean_dec(v_stx_2051_);
                        leanh::lean_dec(v_decl_2050_);
                        v___x_2203_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                        v___x_2204_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2203_, v___y_2053_, v___y_2054_);
                        return v___x_2204_;
                    } else {
                        v___x_2205_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2206_ = l_Lean_Syntax_getArg(v_stx_2051_, v___x_2205_);
                        leanh::lean_dec(v_stx_2051_);
                        v___x_2207_ = l_Lean_Syntax_isNone(v___x_2206_);
                        if v___x_2207_ == 0 {
                            leanh::lean_inc(v___x_2206_);
                            v___x_2208_ = l_Lean_Syntax_matchesNull(v___x_2206_, v___x_2205_);
                            if v___x_2208_ == 0 {
                                leanh::lean_dec(v___x_2206_);
                                leanh::lean_dec(v___x_2201_);
                                leanh::lean_dec(v_decl_2050_);
                                v___x_2209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                v___x_2210_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2209_, v___y_2053_, v___y_2054_);
                                return v___x_2210_;
                            } else {
                                v_id_x3f_2211_ = l_Lean_Syntax_getArg(v___x_2206_, v___x_2048_);
                                leanh::lean_dec(v___x_2206_);
                                v___x_2212_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__12_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
                                leanh::lean_inc(v_id_x3f_2211_);
                                v___x_2213_ = l_Lean_Syntax_isOfKind(v_id_x3f_2211_, v___x_2212_);
                                if v___x_2213_ == 0 {
                                    leanh::lean_dec(v_id_x3f_2211_);
                                    leanh::lean_dec(v___x_2201_);
                                    leanh::lean_dec(v_decl_2050_);
                                    v___x_2214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
                                    v___x_2215_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2214_, v___y_2053_, v___y_2054_);
                                    return v___x_2215_;
                                } else {
                                    v___x_2216_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2216_, 0, v_id_x3f_2211_);
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
                            leanh::lean_dec(v___x_2206_);
                            v___x_2217_ = leanh::lean_box(0);
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
    mut v___x_2221_: *mut leanh::LeanObject,
    mut v___x_2222_: *mut leanh::LeanObject,
    mut v___x_2223_: *mut leanh::LeanObject,
    mut v_decl_2224_: *mut leanh::LeanObject,
    mut v_stx_2225_: *mut leanh::LeanObject,
    mut v_kind_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
    mut v___y_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2230_: u8 = 0;
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2230_ = (leanh::lean_unbox(v_kind_2226_) as u8);
    v_res_2231_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(v___x_2221_, v___x_2222_, v___x_2223_, v_decl_2224_, v_stx_2225_, v_kind_boxed_2230_, v___y_2227_, v___y_2228_);
    leanh::lean_dec(v___y_2228_);
    leanh::lean_dec_ref(v___y_2227_);
    leanh::lean_dec(v___x_2222_);
    return v_res_2231_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
    return v___x_2234_;
}
pub unsafe fn _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(
    mut v___x_2238_: *mut leanh::LeanObject,
    mut v_decl_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
    mut v___y_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
    v___x_2244_ = l_Lean_MessageData_ofName(v___x_2238_);
    v___x_2245_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
    leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
    v___x_2246_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_);
    v___x_2247_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2247_, 0, v___x_2245_);
    leanh::lean_ctor_set(v___x_2247_, 1, v___x_2246_);
    v___x_2248_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v___x_2247_, v___y_2240_, v___y_2241_);
    return v___x_2248_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v___x_2249_: *mut leanh::LeanObject,
    mut v_decl_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___lam__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_(v___x_2249_, v_decl_2250_, v___y_2251_, v___y_2252_);
    leanh::lean_dec(v___y_2252_);
    leanh::lean_dec_ref(v___y_2251_);
    leanh::lean_dec(v_decl_2250_);
    return v_res_2254_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__28_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2328_ = l_Lean_registerBuiltinAttribute(v___x_2327_);
    return v___x_2328_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v_a_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    return v_res_2330_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2331_: *mut leanh::LeanObject,
    mut v_msg_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___redArg(v_msg_2332_, v___y_2333_, v___y_2334_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2337_: *mut leanh::LeanObject,
    mut v_msg_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_throwError___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__0(v_00_u03b1_2337_, v_msg_2338_, v___y_2339_, v___y_2340_);
    leanh::lean_dec(v___y_2340_);
    leanh::lean_dec_ref(v___y_2339_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b1_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_isExporting_2345_: u8,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2344_, v_isExporting_2345_, v___y_2346_, v___y_2347_);
    return v___x_2349_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b1_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_isExporting_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2356_: u8 = 0;
    let mut v_res_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2356_ = (leanh::lean_unbox(v_isExporting_2352_) as u8);
    v_res_2357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_2350_, v_x_2351_, v_isExporting_boxed_2356_, v___y_2353_, v___y_2354_);
    leanh::lean_dec(v___y_2354_);
    leanh::lean_dec_ref(v___y_2353_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2358_: *mut leanh::LeanObject,
    mut v_x_2359_: *mut leanh::LeanObject,
    mut v_when_2360_: u8,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___redArg(v_x_2359_, v_when_2360_, v___y_2361_, v___y_2362_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2365_: *mut leanh::LeanObject,
    mut v_x_2366_: *mut leanh::LeanObject,
    mut v_when_2367_: *mut leanh::LeanObject,
    mut v___y_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2371_: u8 = 0;
    let mut v_res_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2371_ = (leanh::lean_unbox(v_when_2367_) as u8);
    v_res_2372_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__1(v_00_u03b1_2365_, v_x_2366_, v_when_boxed_2371_, v___y_2368_, v___y_2369_);
    leanh::lean_dec(v___y_2369_);
    leanh::lean_dec_ref(v___y_2368_);
    return v_res_2372_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7(
    mut v_00_u03b1_2373_: *mut leanh::LeanObject,
    mut v_name_2374_: *mut leanh::LeanObject,
    mut v_kind_2375_: u8,
    mut v___y_2376_: *mut leanh::LeanObject,
    mut v___y_2377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___redArg(v_name_2374_, v_kind_2375_, v___y_2376_, v___y_2377_);
    return v___x_2379_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7___boxed(
    mut v_00_u03b1_2380_: *mut leanh::LeanObject,
    mut v_name_2381_: *mut leanh::LeanObject,
    mut v_kind_2382_: *mut leanh::LeanObject,
    mut v___y_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2386_: u8 = 0;
    let mut v_res_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2386_ = (leanh::lean_unbox(v_kind_2382_) as u8);
    v_res_2387_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__7(v_00_u03b1_2380_, v_name_2381_, v_kind_boxed_2386_, v___y_2383_, v___y_2384_);
    leanh::lean_dec(v___y_2384_);
    leanh::lean_dec_ref(v___y_2383_);
    return v_res_2387_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8(
    mut v_00_u03b1_2388_: *mut leanh::LeanObject,
    mut v_constName_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___redArg(v_constName_2389_, v___y_2390_, v___y_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b1_2394_: *mut leanh::LeanObject,
    mut v_constName_2395_: *mut leanh::LeanObject,
    mut v___y_2396_: *mut leanh::LeanObject,
    mut v___y_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8(v_00_u03b1_2394_, v_constName_2395_, v___y_2396_, v___y_2397_);
    leanh::lean_dec(v___y_2397_);
    leanh::lean_dec_ref(v___y_2396_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12(
    mut v_00_u03b1_2400_: *mut leanh::LeanObject,
    mut v_ref_2401_: *mut leanh::LeanObject,
    mut v_constName_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___redArg(v_ref_2401_, v_constName_2402_, v___y_2403_, v___y_2404_);
    return v___x_2406_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12___boxed(
    mut v_00_u03b1_2407_: *mut leanh::LeanObject,
    mut v_ref_2408_: *mut leanh::LeanObject,
    mut v_constName_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12(v_00_u03b1_2407_, v_ref_2408_, v_constName_2409_, v___y_2410_, v___y_2411_);
    leanh::lean_dec(v___y_2411_);
    leanh::lean_dec_ref(v___y_2410_);
    leanh::lean_dec(v_ref_2408_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16(
    mut v_00_u03b1_2414_: *mut leanh::LeanObject,
    mut v_ref_2415_: *mut leanh::LeanObject,
    mut v_msg_2416_: *mut leanh::LeanObject,
    mut v_declHint_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
    mut v___y_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___redArg(v_ref_2415_, v_msg_2416_, v_declHint_2417_, v___y_2418_, v___y_2419_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16___boxed(
    mut v_00_u03b1_2422_: *mut leanh::LeanObject,
    mut v_ref_2423_: *mut leanh::LeanObject,
    mut v_msg_2424_: *mut leanh::LeanObject,
    mut v_declHint_2425_: *mut leanh::LeanObject,
    mut v___y_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16(v_00_u03b1_2422_, v_ref_2423_, v_msg_2424_, v_declHint_2425_, v___y_2426_, v___y_2427_);
    leanh::lean_dec(v___y_2427_);
    leanh::lean_dec_ref(v___y_2426_);
    leanh::lean_dec(v_ref_2423_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18(
    mut v_msg_2430_: *mut leanh::LeanObject,
    mut v_declHint_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___redArg(v_msg_2430_, v_declHint_2431_, v___y_2433_);
    return v___x_2435_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18___boxed(
    mut v_msg_2436_: *mut leanh::LeanObject,
    mut v_declHint_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__17_spec__18(v_msg_2436_, v_declHint_2437_, v___y_2438_, v___y_2439_);
    leanh::lean_dec(v___y_2439_);
    leanh::lean_dec_ref(v___y_2438_);
    return v_res_2441_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18(
    mut v_00_u03b1_2442_: *mut leanh::LeanObject,
    mut v_ref_2443_: *mut leanh::LeanObject,
    mut v_msg_2444_: *mut leanh::LeanObject,
    mut v___y_2445_: *mut leanh::LeanObject,
    mut v___y_2446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___redArg(v_ref_2443_, v_msg_2444_, v___y_2445_, v___y_2446_);
    return v___x_2448_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18___boxed(
    mut v_00_u03b1_2449_: *mut leanh::LeanObject,
    mut v_ref_2450_: *mut leanh::LeanObject,
    mut v_msg_2451_: *mut leanh::LeanObject,
    mut v___y_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2__spec__3_spec__6_spec__8_spec__12_spec__16_spec__18(v_00_u03b1_2449_, v_ref_2450_, v_msg_2451_, v___y_2452_, v___y_2453_);
    leanh::lean_dec(v___y_2453_);
    leanh::lean_dec_ref(v___y_2452_);
    leanh::lean_dec(v_ref_2450_);
    return v_res_2455_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___closed__21_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2459_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_;
    v___x_2460_ = l_Lean_addBuiltinDocString(v___x_2458_, v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2____boxed(
    mut v_a_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    return v_res_2462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InheritDoc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_InheritDoc_0__Lean_initFn_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_InheritDoc_0__Lean_initFn___regBuiltin___private_Lean_Elab_InheritDoc_0__Lean_initFn_docString__1_00___x40_Lean_Elab_InheritDoc_986682242____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InheritDoc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InheritDoc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InheritDoc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InheritDoc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_InheritDoc(builtin);
}