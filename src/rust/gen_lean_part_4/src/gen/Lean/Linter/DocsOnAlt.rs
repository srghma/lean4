// Lean compiler output
// Module: Lean.Linter.DocsOnAlt
// Imports: Lean.Parser.Syntax Lean.Data.Options Lean.Elab.Command Lean.Linter.Init Lean.Server.InfoUtils
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_elem___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_find_x3f, l_Lean_Syntax_structEq};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_toArray___redArg, l_Lean_PersistentArray_toList___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::Extension::l_Lean_findInternalDocString_x3f;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_Info_updateContext_x3f, l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag,
    l_Lean_Linter_linterSetsExt, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Syntax::{
    initialize_Lean_Parser_Syntax, runtime_initialize_Lean_Parser_Syntax,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, runtime_initialize_Lean_Server_InfoUtils,
};
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 99, 115, 79, 110, 65, 108, 116, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,18255610267079397070 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15534500847188816770 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<57> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 110, 32, 116, 97, 99, 116, 105, 99, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8071394701935581384 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6326339448686113589 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,16494155296396010253 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,295572273447254829 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_linter_tactic_docsOnAlt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 99, 116, 105, 99, 95, 97, 108, 116, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value) as *mut leanh::LeanObject,4584992172905639687 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value) as *mut leanh::LeanObject,7294395221027647453 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value) as *mut leanh::LeanObject,11509420844586769999 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value) as *mut leanh::LeanObject,9063780239635860524 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value) as *mut leanh::LeanObject,2812521669163367463 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [68, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [96, 32, 105, 115, 32, 105, 103, 110, 111, 114, 101, 100, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 97, 32, 116, 97, 99, 116, 105, 99, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1_value: leanh::LeanStringObject<62> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [68, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 105, 115, 32, 105, 103, 110, 111, 114, 101, 100, 32, 111, 110, 32, 97, 32, 116, 97, 99, 116, 105, 99, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 46, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value: leanh::LeanClosureObject<3> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4424989899264441540 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 111, 99, 115, 79, 110, 65, 108, 116, 0]};
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value) as *mut leanh::LeanObject,12268537686322324213 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,485077014271868640 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,7889426318673355161 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,292406651784905539 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value) as *mut leanh::LeanObject,3550748355209241950 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4961375761850959538 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(
    mut v_name_1057_: *mut leanh::LeanObject,
    mut v_decl_1058_: *mut leanh::LeanObject,
    mut v_ref_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: u8 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_unused_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1061_ = leanh::lean_ctor_get(v_decl_1058_, 0);
                v_descr_1062_ = leanh::lean_ctor_get(v_decl_1058_, 1);
                v_deprecation_x3f_1063_ = leanh::lean_ctor_get(v_decl_1058_, 2);
                v___x_1064_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1065_ = (leanh::lean_unbox(v_defValue_1061_) as u8);
                leanh::lean_ctor_set_uint8(v___x_1064_, 0 as u32, v___x_1065_);
                leanh::lean_inc(v_deprecation_x3f_1063_);
                leanh::lean_inc_ref(v_descr_1062_);
                leanh::lean_inc_n(v_name_1057_, 2);
                v___x_1066_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1066_, 0, v_name_1057_);
                leanh::lean_ctor_set(v___x_1066_, 1, v_ref_1059_);
                leanh::lean_ctor_set(v___x_1066_, 2, v___x_1064_);
                leanh::lean_ctor_set(v___x_1066_, 3, v_descr_1062_);
                leanh::lean_ctor_set(v___x_1066_, 4, v_deprecation_x3f_1063_);
                v___x_1067_ = lean_register_option(v_name_1057_, v___x_1066_);
                if leanh::lean_obj_tag(v___x_1067_) == 0 {
                    v_isSharedCheck_1075_ = (!leanh::lean_is_exclusive(v___x_1067_)) as u8;
                    if v_isSharedCheck_1075_ == 0 {
                        v_unused_1076_ = leanh::lean_ctor_get(v___x_1067_, 0);
                        leanh::lean_dec(v_unused_1076_);
                        v___x_1069_ = v___x_1067_;
                        v_isShared_1070_ = v_isSharedCheck_1075_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1067_);
                        v___x_1069_ = leanh::lean_box(0);
                        v_isShared_1070_ = v_isSharedCheck_1075_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_1057_);
                    v_a_1077_ = leanh::lean_ctor_get(v___x_1067_, 0);
                    v_isSharedCheck_1084_ = (!leanh::lean_is_exclusive(v___x_1067_)) as u8;
                    if v_isSharedCheck_1084_ == 0 {
                        v___x_1079_ = v___x_1067_;
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1077_);
                        leanh::lean_dec(v___x_1067_);
                        v___x_1079_ = leanh::lean_box(0);
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_1061_);
                v___x_1071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1071_, 0, v_name_1057_);
                leanh::lean_ctor_set(v___x_1071_, 1, v_defValue_1061_);
                if v_isShared_1070_ == 0 {
                    leanh::lean_ctor_set(v___x_1069_, 0, v___x_1071_);
                    v___x_1073_ = v___x_1069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
                    v___x_1073_ = v_reuseFailAlloc_1074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1073_;
            }
            3 => {
                if v_isShared_1080_ == 0 {
                    v___x_1082_ = v___x_1079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
                    v___x_1082_ = v_reuseFailAlloc_1083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1085_: *mut leanh::LeanObject,
    mut v_decl_1086_: *mut leanh::LeanObject,
    mut v_ref_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(v_name_1085_, v_decl_1086_, v_ref_1087_);
    leanh::lean_dec_ref(v_decl_1086_);
    return v_res_1089_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_;
    v___x_1113_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_;
    v___x_1114_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_;
    v___x_1115_ = l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(v___x_1112_, v___x_1113_, v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4____boxed(
    mut v_a_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_();
    return v_res_1117_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(
    mut v_o_1118_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: u8 = 0;
    v___x_1119_ = l_Lean_Linter_linter_tactic_docsOnAlt;
    v___x_1120_ = l_Lean_Linter_getLinterValue(v___x_1119_, v_o_1118_);
    return v___x_1120_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt___boxed(
    mut v_o_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: u8 = 0;
    let mut v_r_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(v_o_1121_);
    leanh::lean_dec_ref(v_o_1121_);
    v_r_1123_ = leanh::lean_box((v_res_1122_) as usize);
    return v_r_1123_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr(
    mut v_a_1132_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    v___x_1133_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3;
    v___x_1134_ = l_Lean_Syntax_isOfKind(v_a_1132_, v___x_1133_);
    return v___x_1134_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___boxed(
    mut v_a_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1136_: u8 = 0;
    let mut v_r_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr(v_a_1135_);
    v_r_1137_ = leanh::lean_box((v_res_1136_) as usize);
    return v_r_1137_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0(
    mut v_x_1145_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    v___x_1146_ = l_Lean_Syntax_getKind(v_x_1145_);
    v___x_1147_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2;
    v___x_1148_ = lean_name_eq(v___x_1146_, v___x_1147_);
    leanh::lean_dec(v___x_1146_);
    return v___x_1148_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___boxed(
    mut v_x_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1150_: u8 = 0;
    let mut v_r_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0(v_x_1149_);
    v_r_1151_ = leanh::lean_box((v_res_1150_) as usize);
    return v_r_1151_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1(
    mut v_x_1158_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    v___x_1159_ = l_Lean_Syntax_getKind(v_x_1158_);
    v___x_1160_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1;
    v___x_1161_ = lean_name_eq(v___x_1159_, v___x_1160_);
    leanh::lean_dec(v___x_1159_);
    return v___x_1161_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___boxed(
    mut v_x_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1163_: u8 = 0;
    let mut v_r_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1(v_x_1162_);
    v_r_1164_ = leanh::lean_box((v_res_1163_) as usize);
    return v_r_1164_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(
    mut v_x_1184_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    v___x_1185_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0;
    v___x_1186_ = l_Lean_Syntax_getKind(v_x_1184_);
    v___x_1187_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6;
    v___x_1188_ = l_List_elem___redArg(v___x_1185_, v___x_1186_, v___x_1187_);
    return v___x_1188_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed(
    mut v_x_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1190_: u8 = 0;
    let mut v_r_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(v_x_1189_);
    v_r_1191_ = leanh::lean_box((v_res_1190_) as usize);
    return v_r_1191_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(
    mut v_o_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = lean_st_ref_get(v___y_1193_);
    v_env_1196_ = leanh::lean_ctor_get(v___x_1195_, 0);
    leanh::lean_inc_ref(v_env_1196_);
    leanh::lean_dec(v___x_1195_);
    v___x_1197_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_1198_ = leanh::lean_ctor_get(v___x_1197_, 0);
    v_asyncMode_1199_ = leanh::lean_ctor_get(v_toEnvExtension_1198_, 2);
    v___x_1200_ = leanh::lean_box(1);
    v___x_1201_ = leanh::lean_box(0);
    v_linterSets_1202_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1200_,
        v___x_1197_,
        v_env_1196_,
        v_asyncMode_1199_,
        v___x_1201_,
    );
    v___x_1203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1203_, 0, v_o_1192_);
    leanh::lean_ctor_set(v___x_1203_, 1, v_linterSets_1202_);
    v___x_1204_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1204_, 0, v___x_1203_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg___boxed(
    mut v_o_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_o_1205_, v___y_1206_);
    leanh::lean_dec(v___y_1206_);
    return v_res_1208_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = lean_st_ref_get(v___y_1210_);
    v_scopes_1213_ = leanh::lean_ctor_get(v___x_1212_, 2);
    leanh::lean_inc(v_scopes_1213_);
    leanh::lean_dec(v___x_1212_);
    v___x_1214_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1215_ = l_List_head_x21___redArg(v___x_1214_, v_scopes_1213_);
    leanh::lean_dec(v_scopes_1213_);
    v_opts_1216_ = leanh::lean_ctor_get(v___x_1215_, 1);
    leanh::lean_inc_ref(v_opts_1216_);
    leanh::lean_dec(v___x_1215_);
    v___x_1217_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_opts_1216_, v___y_1210_);
    return v___x_1217_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0___boxed(
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v___y_1218_, v___y_1219_);
    leanh::lean_dec(v___y_1219_);
    leanh::lean_dec_ref(v___y_1218_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0(
    mut v___y_1223_: u8,
    mut v_suppressElabErrors_1224_: u8,
    mut v_x_1225_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1225_) == 1 {
        let mut v_pre_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_1226_ = leanh::lean_ctor_get(v_x_1225_, 0);
        if leanh::lean_obj_tag(v_pre_1226_) == 0 {
            let mut v_str_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: u8 = 0;
            v_str_1227_ = leanh::lean_ctor_get(v_x_1225_, 1);
            v___x_1228_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0;
            v___x_1229_ = lean_string_dec_eq(v_str_1227_, v___x_1228_);
            if v___x_1229_ == 0 {
                return v___y_1223_;
            } else {
                return v_suppressElabErrors_1224_;
            }
        } else {
            return v___y_1223_;
        }
    } else {
        return v___y_1223_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___boxed(
    mut v___y_1230_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_1231_: *mut leanh::LeanObject,
    mut v_x_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8751__boxed_1233_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1234_: u8 = 0;
    let mut v_res_1235_: u8 = 0;
    let mut v_r_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_8751__boxed_1233_ = (leanh::lean_unbox(v___y_1230_) as u8);
    v_suppressElabErrors_boxed_1234_ = (leanh::lean_unbox(v_suppressElabErrors_1231_) as u8);
    v_res_1235_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0(v___y_8751__boxed_1233_, v_suppressElabErrors_boxed_1234_, v_x_1232_);
    leanh::lean_dec(v_x_1232_);
    v_r_1236_ = leanh::lean_box((v_res_1235_) as usize);
    return v_r_1236_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1237_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0);
    v___x_1239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    return v___x_1239_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1);
    v___x_1241_ = leanh::lean_unsigned_to_nat(0);
    v___x_1242_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1242_, 0, v___x_1241_);
    leanh::lean_ctor_set(v___x_1242_, 1, v___x_1241_);
    leanh::lean_ctor_set(v___x_1242_, 2, v___x_1241_);
    leanh::lean_ctor_set(v___x_1242_, 3, v___x_1241_);
    leanh::lean_ctor_set(v___x_1242_, 4, v___x_1240_);
    leanh::lean_ctor_set(v___x_1242_, 5, v___x_1240_);
    leanh::lean_ctor_set(v___x_1242_, 6, v___x_1240_);
    leanh::lean_ctor_set(v___x_1242_, 7, v___x_1240_);
    leanh::lean_ctor_set(v___x_1242_, 8, v___x_1240_);
    leanh::lean_ctor_set(v___x_1242_, 9, v___x_1240_);
    return v___x_1242_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = leanh::lean_unsigned_to_nat(32);
    v___x_1244_ = lean_mk_empty_array_with_capacity(v___x_1243_);
    v___x_1245_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1245_, 0, v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = 5usize;
    v___x_1247_ = leanh::lean_unsigned_to_nat(0);
    v___x_1248_ = leanh::lean_unsigned_to_nat(32);
    v___x_1249_ = lean_mk_empty_array_with_capacity(v___x_1248_);
    v___x_1250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3);
    v___x_1251_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 1, v___x_1249_);
    leanh::lean_ctor_set(v___x_1251_, 2, v___x_1247_);
    leanh::lean_ctor_set(v___x_1251_, 3, v___x_1247_);
    leanh::lean_ctor_set_usize(v___x_1251_, 4, v___x_1246_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = leanh::lean_box(1);
    v___x_1253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4);
    v___x_1254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1);
    v___x_1255_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1255_, 0, v___x_1254_);
    leanh::lean_ctor_set(v___x_1255_, 1, v___x_1253_);
    leanh::lean_ctor_set(v___x_1255_, 2, v___x_1252_);
    return v___x_1255_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(
    mut v_msgData_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = lean_st_ref_get(v___y_1257_);
    v_env_1260_ = leanh::lean_ctor_get(v___x_1259_, 0);
    leanh::lean_inc_ref(v_env_1260_);
    leanh::lean_dec(v___x_1259_);
    v___x_1261_ = lean_st_ref_get(v___y_1257_);
    v_scopes_1262_ = leanh::lean_ctor_get(v___x_1261_, 2);
    leanh::lean_inc(v_scopes_1262_);
    leanh::lean_dec(v___x_1261_);
    v___x_1263_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1264_ = l_List_head_x21___redArg(v___x_1263_, v_scopes_1262_);
    leanh::lean_dec(v_scopes_1262_);
    v_opts_1265_ = leanh::lean_ctor_get(v___x_1264_, 1);
    leanh::lean_inc_ref(v_opts_1265_);
    leanh::lean_dec(v___x_1264_);
    v___x_1266_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2);
    v___x_1267_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5);
    v___x_1268_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v_env_1260_);
    leanh::lean_ctor_set(v___x_1268_, 1, v___x_1266_);
    leanh::lean_ctor_set(v___x_1268_, 2, v___x_1267_);
    leanh::lean_ctor_set(v___x_1268_, 3, v_opts_1265_);
    v___x_1269_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1269_, 0, v___x_1268_);
    leanh::lean_ctor_set(v___x_1269_, 1, v_msgData_1256_);
    v___x_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
    return v___x_1270_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_msgData_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v_msgData_1271_, v___y_1272_);
    leanh::lean_dec(v___y_1272_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(
    mut v_opts_1275_: *mut leanh::LeanObject,
    mut v_opt_1276_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1277_ = leanh::lean_ctor_get(v_opt_1276_, 0);
    v_defValue_1278_ = leanh::lean_ctor_get(v_opt_1276_, 1);
    v_map_1279_ = leanh::lean_ctor_get(v_opts_1275_, 0);
    v___x_1280_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1279_,
            v_name_1277_,
        );
    if leanh::lean_obj_tag(v___x_1280_) == 0 {
        let mut v___x_1281_: u8 = 0;
        v___x_1281_ = (leanh::lean_unbox(v_defValue_1278_) as u8);
        return v___x_1281_;
    } else {
        let mut v_val_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1282_ = leanh::lean_ctor_get(v___x_1280_, 0);
        leanh::lean_inc(v_val_1282_);
        leanh::lean_dec_ref_known(v___x_1280_, 1);
        if leanh::lean_obj_tag(v_val_1282_) == 1 {
            let mut v_v_1283_: u8 = 0;
            v_v_1283_ = leanh::lean_ctor_get_uint8(v_val_1282_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1282_, 0);
            return v_v_1283_;
        } else {
            let mut v___x_1284_: u8 = 0;
            leanh::lean_dec(v_val_1282_);
            v___x_1284_ = (leanh::lean_unbox(v_defValue_1278_) as u8);
            return v___x_1284_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8___boxed(
    mut v_opts_1285_: *mut leanh::LeanObject,
    mut v_opt_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1287_: u8 = 0;
    let mut v_r_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1287_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(v_opts_1285_, v_opt_1286_);
    leanh::lean_dec_ref(v_opt_1286_);
    leanh::lean_dec_ref(v_opts_1285_);
    v_r_1288_ = leanh::lean_box((v_res_1287_) as usize);
    return v_r_1288_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(
    mut v_ref_1290_: *mut leanh::LeanObject,
    mut v_msgData_1291_: *mut leanh::LeanObject,
    mut v_severity_1292_: u8,
    mut v_isSilent_1293_: u8,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: u8 = 0;
    let mut v___y_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1303_: u8 = 0;
    let mut v___y_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut v_a_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1359_: u8 = 0;
    let mut v___y_1361_: u8 = 0;
    let mut v___y_1362_: u8 = 0;
    let mut v___y_1363_: u8 = 0;
    let mut v___y_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1368_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v___y_1389_: u8 = 0;
    let mut v___y_1390_: u8 = 0;
    let mut v___y_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1392_: u8 = 0;
    let mut v___y_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1397_: u8 = 0;
    let mut v___y_1398_: u8 = 0;
    let mut v___y_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v___x_1414_: u8 = 0;
    let mut v___y_1416_: u8 = 0;
    let mut v___y_1417_: u8 = 0;
    let mut v___y_1418_: u8 = 0;
    let mut v___y_1420_: u8 = 0;
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: u8 = 0;
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1414_ = 2;
                v___x_1432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1292_, v___x_1414_);
                if v___x_1432_ == 0 {
                    v___y_1420_ = v___x_1432_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_1291_);
                    v___x_1433_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1291_);
                    v___y_1420_ = v___x_1433_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1306_ = l_Lean_Elab_Command_getScope___redArg(v___y_1305_);
                if leanh::lean_obj_tag(v___x_1306_) == 0 {
                    v_a_1307_ = leanh::lean_ctor_get(v___x_1306_, 0);
                    leanh::lean_inc(v_a_1307_);
                    leanh::lean_dec_ref_known(v___x_1306_, 1);
                    v___x_1308_ = l_Lean_Elab_Command_getScope___redArg(v___y_1305_);
                    if leanh::lean_obj_tag(v___x_1308_) == 0 {
                        v_a_1309_ = leanh::lean_ctor_get(v___x_1308_, 0);
                        v_isSharedCheck_1343_ =
                            (!leanh::lean_is_exclusive(v___x_1308_)) as u8;
                        if v_isSharedCheck_1343_ == 0 {
                            v___x_1311_ = v___x_1308_;
                            v_isShared_1312_ = v_isSharedCheck_1343_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1309_);
                            leanh::lean_dec(v___x_1308_);
                            v___x_1311_ = leanh::lean_box(0);
                            v_isShared_1312_ = v_isSharedCheck_1343_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1307_);
                        leanh::lean_dec_ref(v___y_1302_);
                        leanh::lean_dec_ref(v___y_1301_);
                        leanh::lean_dec(v___y_1300_);
                        v_a_1344_ = leanh::lean_ctor_get(v___x_1308_, 0);
                        v_isSharedCheck_1351_ =
                            (!leanh::lean_is_exclusive(v___x_1308_)) as u8;
                        if v_isSharedCheck_1351_ == 0 {
                            v___x_1346_ = v___x_1308_;
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1344_);
                            leanh::lean_dec(v___x_1308_);
                            v___x_1346_ = leanh::lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_1302_);
                    leanh::lean_dec_ref(v___y_1301_);
                    leanh::lean_dec(v___y_1300_);
                    v_a_1352_ = leanh::lean_ctor_get(v___x_1306_, 0);
                    v_isSharedCheck_1359_ = (!leanh::lean_is_exclusive(v___x_1306_)) as u8;
                    if v_isSharedCheck_1359_ == 0 {
                        v___x_1354_ = v___x_1306_;
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1352_);
                        leanh::lean_dec(v___x_1306_);
                        v___x_1354_ = leanh::lean_box(0);
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1313_ = lean_st_ref_take(v___y_1305_);
                v_currNamespace_1314_ = leanh::lean_ctor_get(v_a_1307_, 2);
                leanh::lean_inc(v_currNamespace_1314_);
                leanh::lean_dec(v_a_1307_);
                v_openDecls_1315_ = leanh::lean_ctor_get(v_a_1309_, 3);
                leanh::lean_inc(v_openDecls_1315_);
                leanh::lean_dec(v_a_1309_);
                v_env_1316_ = leanh::lean_ctor_get(v___x_1313_, 0);
                v_messages_1317_ = leanh::lean_ctor_get(v___x_1313_, 1);
                v_scopes_1318_ = leanh::lean_ctor_get(v___x_1313_, 2);
                v_usedQuotCtxts_1319_ = leanh::lean_ctor_get(v___x_1313_, 3);
                v_nextMacroScope_1320_ = leanh::lean_ctor_get(v___x_1313_, 4);
                v_maxRecDepth_1321_ = leanh::lean_ctor_get(v___x_1313_, 5);
                v_ngen_1322_ = leanh::lean_ctor_get(v___x_1313_, 6);
                v_auxDeclNGen_1323_ = leanh::lean_ctor_get(v___x_1313_, 7);
                v_infoState_1324_ = leanh::lean_ctor_get(v___x_1313_, 8);
                v_traceState_1325_ = leanh::lean_ctor_get(v___x_1313_, 9);
                v_snapshotTasks_1326_ = leanh::lean_ctor_get(v___x_1313_, 10);
                v_isSharedCheck_1342_ = (!leanh::lean_is_exclusive(v___x_1313_)) as u8;
                if v_isSharedCheck_1342_ == 0 {
                    v___x_1328_ = v___x_1313_;
                    v_isShared_1329_ = v_isSharedCheck_1342_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1326_);
                    leanh::lean_inc(v_traceState_1325_);
                    leanh::lean_inc(v_infoState_1324_);
                    leanh::lean_inc(v_auxDeclNGen_1323_);
                    leanh::lean_inc(v_ngen_1322_);
                    leanh::lean_inc(v_maxRecDepth_1321_);
                    leanh::lean_inc(v_nextMacroScope_1320_);
                    leanh::lean_inc(v_usedQuotCtxts_1319_);
                    leanh::lean_inc(v_scopes_1318_);
                    leanh::lean_inc(v_messages_1317_);
                    leanh::lean_inc(v_env_1316_);
                    leanh::lean_dec(v___x_1313_);
                    v___x_1328_ = leanh::lean_box(0);
                    v_isShared_1329_ = v_isSharedCheck_1342_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1330_, 0, v_currNamespace_1314_);
                leanh::lean_ctor_set(v___x_1330_, 1, v_openDecls_1315_);
                v___x_1331_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
                leanh::lean_ctor_set(v___x_1331_, 1, v___y_1302_);
                leanh::lean_inc_ref(v___y_1298_);
                leanh::lean_inc_ref(v___y_1304_);
                v___x_1332_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_1332_, 0, v___y_1304_);
                leanh::lean_ctor_set(v___x_1332_, 1, v___y_1301_);
                leanh::lean_ctor_set(v___x_1332_, 2, v___y_1300_);
                leanh::lean_ctor_set(v___x_1332_, 3, v___y_1298_);
                leanh::lean_ctor_set(v___x_1332_, 4, v___x_1331_);
                leanh::lean_ctor_set_uint8(
                    v___x_1332_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_1303_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1332_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1299_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1332_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1293_,
                );
                v___x_1333_ = l_Lean_MessageLog_add(v___x_1332_, v_messages_1317_);
                if v_isShared_1329_ == 0 {
                    leanh::lean_ctor_set(v___x_1328_, 1, v___x_1333_);
                    v___x_1335_ = v___x_1328_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_env_1316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_scopes_1318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_usedQuotCtxts_1319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_nextMacroScope_1320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 5, v_maxRecDepth_1321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 6, v_ngen_1322_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 7, v_auxDeclNGen_1323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 8, v_infoState_1324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 9, v_traceState_1325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 10, v_snapshotTasks_1326_);
                    v___x_1335_ = v_reuseFailAlloc_1341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1336_ = lean_st_ref_set(v___y_1305_, v___x_1335_);
                v___x_1337_ = leanh::lean_box(0);
                if v_isShared_1312_ == 0 {
                    leanh::lean_ctor_set(v___x_1311_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1339_;
            }
            6 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1349_;
            }
            8 => {
                if v_isShared_1355_ == 0 {
                    v___x_1357_ = v___x_1354_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1358_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
                    v___x_1357_ = v_reuseFailAlloc_1358_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1357_;
            }
            10 => {
                v_fileName_1366_ = leanh::lean_ctor_get(v___y_1294_, 0);
                v_fileMap_1367_ = leanh::lean_ctor_get(v___y_1294_, 1);
                v_suppressElabErrors_1368_ = leanh::lean_ctor_get_uint8(
                    v___y_1294_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v___x_1369_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1291_,
                    );
                v___x_1370_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v___x_1369_, v___y_1295_);
                v_a_1371_ = leanh::lean_ctor_get(v___x_1370_, 0);
                v_isSharedCheck_1387_ = (!leanh::lean_is_exclusive(v___x_1370_)) as u8;
                if v_isSharedCheck_1387_ == 0 {
                    v___x_1373_ = v___x_1370_;
                    v_isShared_1374_ = v_isSharedCheck_1387_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1371_);
                    leanh::lean_dec(v___x_1370_);
                    v___x_1373_ = leanh::lean_box(0);
                    v_isShared_1374_ = v_isSharedCheck_1387_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc_ref_n(v_fileMap_1367_, 2);
                v___x_1375_ = l_Lean_FileMap_toPosition(v_fileMap_1367_, v___y_1364_);
                leanh::lean_dec(v___y_1364_);
                v___x_1376_ = l_Lean_FileMap_toPosition(v_fileMap_1367_, v___y_1365_);
                leanh::lean_dec(v___y_1365_);
                v___x_1377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                v___x_1378_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0;
                if v_suppressElabErrors_1368_ == 0 {
                    leanh::lean_del_object(v___x_1373_);
                    v___y_1298_ = v___x_1378_;
                    v___y_1299_ = v___y_1362_;
                    v___y_1300_ = v___x_1377_;
                    v___y_1301_ = v___x_1375_;
                    v___y_1302_ = v_a_1371_;
                    v___y_1303_ = v___y_1363_;
                    v___y_1304_ = v_fileName_1366_;
                    v___y_1305_ = v___y_1295_;
                    state = 1;
                    continue;
                } else {
                    v___x_1379_ = leanh::lean_box((v___y_1361_) as usize);
                    v___x_1380_ = leanh::lean_box((v_suppressElabErrors_1368_) as usize);
                    v___f_1381_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_1381_, 0, v___x_1379_);
                    leanh::lean_closure_set(v___f_1381_, 1, v___x_1380_);
                    leanh::lean_inc(v_a_1371_);
                    v___x_1382_ = l_Lean_MessageData_hasTag(v___f_1381_, v_a_1371_);
                    if v___x_1382_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1377_, 1);
                        leanh::lean_dec_ref(v___x_1375_);
                        leanh::lean_dec(v_a_1371_);
                        v___x_1383_ = leanh::lean_box(0);
                        if v_isShared_1374_ == 0 {
                            leanh::lean_ctor_set(v___x_1373_, 0, v___x_1383_);
                            v___x_1385_ = v___x_1373_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1386_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
                            v___x_1385_ = v_reuseFailAlloc_1386_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1373_);
                        v___y_1298_ = v___x_1378_;
                        v___y_1299_ = v___y_1362_;
                        v___y_1300_ = v___x_1377_;
                        v___y_1301_ = v___x_1375_;
                        v___y_1302_ = v_a_1371_;
                        v___y_1303_ = v___y_1363_;
                        v___y_1304_ = v_fileName_1366_;
                        v___y_1305_ = v___y_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1385_;
            }
            13 => {
                v___x_1394_ = l_Lean_Syntax_getTailPos_x3f(v___y_1391_, v___y_1392_);
                leanh::lean_dec(v___y_1391_);
                if leanh::lean_obj_tag(v___x_1394_) == 0 {
                    leanh::lean_inc(v___y_1393_);
                    v___y_1361_ = v___y_1389_;
                    v___y_1362_ = v___y_1390_;
                    v___y_1363_ = v___y_1392_;
                    v___y_1364_ = v___y_1393_;
                    v___y_1365_ = v___y_1393_;
                    state = 10;
                    continue;
                } else {
                    v_val_1395_ = leanh::lean_ctor_get(v___x_1394_, 0);
                    leanh::lean_inc(v_val_1395_);
                    leanh::lean_dec_ref_known(v___x_1394_, 1);
                    v___y_1361_ = v___y_1389_;
                    v___y_1362_ = v___y_1390_;
                    v___y_1363_ = v___y_1392_;
                    v___y_1364_ = v___y_1393_;
                    v___y_1365_ = v_val_1395_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1400_ = l_Lean_Elab_Command_getRef___redArg(v___y_1294_);
                if leanh::lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = leanh::lean_ctor_get(v___x_1400_, 0);
                    leanh::lean_inc(v_a_1401_);
                    leanh::lean_dec_ref_known(v___x_1400_, 1);
                    v_ref_1402_ = l_Lean_replaceRef(v_ref_1290_, v_a_1401_);
                    leanh::lean_dec(v_a_1401_);
                    v___x_1403_ = l_Lean_Syntax_getPos_x3f(v_ref_1402_, v___y_1398_);
                    if leanh::lean_obj_tag(v___x_1403_) == 0 {
                        v___x_1404_ = leanh::lean_unsigned_to_nat(0);
                        v___y_1389_ = v___y_1397_;
                        v___y_1390_ = v___y_1399_;
                        v___y_1391_ = v_ref_1402_;
                        v___y_1392_ = v___y_1398_;
                        v___y_1393_ = v___x_1404_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1405_ = leanh::lean_ctor_get(v___x_1403_, 0);
                        leanh::lean_inc(v_val_1405_);
                        leanh::lean_dec_ref_known(v___x_1403_, 1);
                        v___y_1389_ = v___y_1397_;
                        v___y_1390_ = v___y_1399_;
                        v___y_1391_ = v_ref_1402_;
                        v___y_1392_ = v___y_1398_;
                        v___y_1393_ = v_val_1405_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_1291_);
                    v_a_1406_ = leanh::lean_ctor_get(v___x_1400_, 0);
                    v_isSharedCheck_1413_ = (!leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1408_ = v___x_1400_;
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1406_);
                        leanh::lean_dec(v___x_1400_);
                        v___x_1408_ = leanh::lean_box(0);
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1409_ == 0 {
                    v___x_1411_ = v___x_1408_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1411_;
            }
            17 => {
                if v___y_1418_ == 0 {
                    v___y_1397_ = v___y_1416_;
                    v___y_1398_ = v___y_1417_;
                    v___y_1399_ = v_severity_1292_;
                    state = 14;
                    continue;
                } else {
                    v___y_1397_ = v___y_1416_;
                    v___y_1398_ = v___y_1417_;
                    v___y_1399_ = v___x_1414_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1420_ == 0 {
                    v___x_1421_ = lean_st_ref_get(v___y_1295_);
                    v_scopes_1422_ = leanh::lean_ctor_get(v___x_1421_, 2);
                    leanh::lean_inc(v_scopes_1422_);
                    leanh::lean_dec(v___x_1421_);
                    v___x_1423_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1424_ = l_List_head_x21___redArg(v___x_1423_, v_scopes_1422_);
                    leanh::lean_dec(v_scopes_1422_);
                    v_opts_1425_ = leanh::lean_ctor_get(v___x_1424_, 1);
                    leanh::lean_inc_ref(v_opts_1425_);
                    leanh::lean_dec(v___x_1424_);
                    v___x_1426_ = 1;
                    v___x_1427_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1292_, v___x_1426_);
                    if v___x_1427_ == 0 {
                        leanh::lean_dec_ref(v_opts_1425_);
                        v___y_1416_ = v___y_1420_;
                        v___y_1417_ = v___y_1420_;
                        v___y_1418_ = v___x_1427_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1428_ = l_Lean_warningAsError;
                        v___x_1429_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(v_opts_1425_, v___x_1428_);
                        leanh::lean_dec_ref(v_opts_1425_);
                        v___y_1416_ = v___y_1420_;
                        v___y_1417_ = v___y_1420_;
                        v___y_1418_ = v___x_1429_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_1291_);
                    v___x_1430_ = leanh::lean_box(0);
                    v___x_1431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1431_, 0, v___x_1430_);
                    return v___x_1431_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___boxed(
    mut v_ref_1434_: *mut leanh::LeanObject,
    mut v_msgData_1435_: *mut leanh::LeanObject,
    mut v_severity_1436_: *mut leanh::LeanObject,
    mut v_isSilent_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_1441_: u8 = 0;
    let mut v_isSilent_boxed_1442_: u8 = 0;
    let mut v_res_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1441_ = (leanh::lean_unbox(v_severity_1436_) as u8);
    v_isSilent_boxed_1442_ = (leanh::lean_unbox(v_isSilent_1437_) as u8);
    v_res_1443_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(v_ref_1434_, v_msgData_1435_, v_severity_boxed_1441_, v_isSilent_boxed_1442_, v___y_1438_, v___y_1439_);
    leanh::lean_dec(v___y_1439_);
    leanh::lean_dec_ref(v___y_1438_);
    leanh::lean_dec(v_ref_1434_);
    return v_res_1443_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(
    mut v_ref_1444_: *mut leanh::LeanObject,
    mut v_msgData_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = 1;
    v___x_1450_ = 0;
    v___x_1451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(v_ref_1444_, v_msgData_1445_, v___x_1449_, v___x_1450_, v___y_1446_, v___y_1447_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2___boxed(
    mut v_ref_1452_: *mut leanh::LeanObject,
    mut v_msgData_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
    mut v___y_1455_: *mut leanh::LeanObject,
    mut v___y_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1457_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(v_ref_1452_, v_msgData_1453_, v___y_1454_, v___y_1455_);
    leanh::lean_dec(v___y_1455_);
    leanh::lean_dec_ref(v___y_1454_);
    leanh::lean_dec(v_ref_1452_);
    return v_res_1457_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0;
    v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2;
    v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(
    mut v_linterOption_1464_: *mut leanh::LeanObject,
    mut v_stx_1465_: *mut leanh::LeanObject,
    mut v_msg_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v_unused_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1470_ = leanh::lean_ctor_get(v_linterOption_1464_, 0);
                v_isSharedCheck_1487_ =
                    (!leanh::lean_is_exclusive(v_linterOption_1464_)) as u8;
                if v_isSharedCheck_1487_ == 0 {
                    v_unused_1488_ = leanh::lean_ctor_get(v_linterOption_1464_, 1);
                    leanh::lean_dec(v_unused_1488_);
                    v___x_1472_ = v_linterOption_1464_;
                    v_isShared_1473_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_1470_);
                    leanh::lean_dec(v_linterOption_1464_);
                    v___x_1472_ = leanh::lean_box(0);
                    v_isShared_1473_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1);
                leanh::lean_inc(v_name_1470_);
                v___x_1475_ = l_Lean_MessageData_ofName(v_name_1470_);
                if v_isShared_1473_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1472_, 7);
                    leanh::lean_ctor_set(v___x_1472_, 1, v___x_1475_);
                    leanh::lean_ctor_set(v___x_1472_, 0, v___x_1474_);
                    v___x_1477_ = v___x_1472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3);
                v___x_1479_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1479_, 0, v___x_1477_);
                leanh::lean_ctor_set(v___x_1479_, 1, v___x_1478_);
                v_disable_1480_ = l_Lean_MessageData_note(v___x_1479_);
                v___x_1481_ = l_Lean_Linter_linterMessageTag;
                v___x_1482_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1482_, 0, v_msg_1466_);
                leanh::lean_ctor_set(v___x_1482_, 1, v_disable_1480_);
                v___x_1483_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1483_, 0, v___x_1481_);
                leanh::lean_ctor_set(v___x_1483_, 1, v___x_1482_);
                v___x_1484_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1484_, 0, v_name_1470_);
                leanh::lean_ctor_set(v___x_1484_, 1, v___x_1483_);
                v___x_1485_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(v_stx_1465_, v___x_1484_, v___y_1467_, v___y_1468_);
                return v___x_1485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___boxed(
    mut v_linterOption_1489_: *mut leanh::LeanObject,
    mut v_stx_1490_: *mut leanh::LeanObject,
    mut v_msg_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
    mut v___y_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v_linterOption_1489_, v_stx_1490_, v_msg_1491_, v___y_1492_, v___y_1493_);
    leanh::lean_dec(v___y_1493_);
    leanh::lean_dec_ref(v___y_1492_);
    leanh::lean_dec(v_stx_1490_);
    return v_res_1495_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(
    mut v_a_1496_: *mut leanh::LeanObject,
    mut v_as_1497_: *mut leanh::LeanObject,
    mut v_i_1498_: usize,
    mut v_stop_1499_: usize,
) -> u8 {
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1500_ = lean_usize_dec_eq(v_i_1498_, v_stop_1499_);
                if v___x_1500_ == 0 {
                    v___x_1501_ = lean_array_uget_borrowed(v_as_1497_, v_i_1498_);
                    leanh::lean_inc(v___x_1501_);
                    leanh::lean_inc(v_a_1496_);
                    v___x_1502_ = l_Lean_Syntax_structEq(v_a_1496_, v___x_1501_);
                    if v___x_1502_ == 0 {
                        v___x_1503_ = 1usize;
                        v___x_1504_ = lean_usize_add(v_i_1498_, v___x_1503_);
                        v_i_1498_ = v___x_1504_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_1496_);
                        return v___x_1502_;
                    }
                } else {
                    leanh::lean_dec(v_a_1496_);
                    v___x_1506_ = 0;
                    return v___x_1506_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4___boxed(
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_as_1508_: *mut leanh::LeanObject,
    mut v_i_1509_: *mut leanh::LeanObject,
    mut v_stop_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1511_: usize = 0;
    let mut v_stop_boxed_1512_: usize = 0;
    let mut v_res_1513_: u8 = 0;
    let mut v_r_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1511_ = leanh::lean_unbox_usize(v_i_1509_);
    leanh::lean_dec(v_i_1509_);
    v_stop_boxed_1512_ = leanh::lean_unbox_usize(v_stop_1510_);
    leanh::lean_dec(v_stop_1510_);
    v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(v_a_1507_, v_as_1508_, v_i_boxed_1511_, v_stop_boxed_1512_);
    leanh::lean_dec_ref(v_as_1508_);
    v_r_1514_ = leanh::lean_box((v_res_1513_) as usize);
    return v_r_1514_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(
    mut v_as_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: u8 = 0;
    v___x_1517_ = leanh::lean_unsigned_to_nat(0);
    v___x_1518_ = lean_array_get_size(v_as_1515_);
    v___x_1519_ = lean_nat_dec_lt(v___x_1517_, v___x_1518_);
    if v___x_1519_ == 0 {
        leanh::lean_dec(v_a_1516_);
        return v___x_1519_;
    } else {
        if v___x_1519_ == 0 {
            leanh::lean_dec(v_a_1516_);
            return v___x_1519_;
        } else {
            let mut v___x_1520_: usize = 0;
            let mut v___x_1521_: usize = 0;
            let mut v___x_1522_: u8 = 0;
            v___x_1520_ = 0usize;
            v___x_1521_ = lean_usize_of_nat(v___x_1518_);
            v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(v_a_1516_, v_as_1515_, v___x_1520_, v___x_1521_);
            return v___x_1522_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___boxed(
    mut v_as_1523_: *mut leanh::LeanObject,
    mut v_a_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1525_: u8 = 0;
    let mut v_r_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v_as_1523_, v_a_1524_);
    leanh::lean_dec_ref(v_as_1523_);
    v_r_1526_ = leanh::lean_box((v_res_1525_) as usize);
    return v_r_1526_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0;
    v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2;
    v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1(
    mut v___x_1533_: *mut leanh::LeanObject,
    mut v___x_1534_: u8,
    mut v_ci_1535_: *mut leanh::LeanObject,
    mut v_info_1536_: *mut leanh::LeanObject,
    mut v_x_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v_toElabInfo_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_a_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v_ref_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_unused_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_info_1536_) == 1 {
                    v_i_1541_ = leanh::lean_ctor_get(v_info_1536_, 0);
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v_info_1536_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1543_ = v_info_1536_;
                        v_isShared_1544_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_1541_);
                        leanh::lean_dec(v_info_1536_);
                        v___x_1543_ = leanh::lean_box(0);
                        v_isShared_1544_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_info_1536_);
                    leanh::lean_dec_ref(v_ci_1535_);
                    v___x_1604_ = leanh::lean_box(0);
                    v___x_1605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1605_, 0, v___x_1604_);
                    return v___x_1605_;
                }
            }
            1 => {
                v_toElabInfo_1545_ = leanh::lean_ctor_get(v_i_1541_, 0);
                leanh::lean_inc_ref(v_toElabInfo_1545_);
                v_expr_1546_ = leanh::lean_ctor_get(v_i_1541_, 3);
                leanh::lean_inc_ref(v_expr_1546_);
                leanh::lean_dec_ref(v_i_1541_);
                v_stx_1547_ = leanh::lean_ctor_get(v_toElabInfo_1545_, 1);
                v_isSharedCheck_1601_ =
                    (!leanh::lean_is_exclusive(v_toElabInfo_1545_)) as u8;
                if v_isSharedCheck_1601_ == 0 {
                    v_unused_1602_ = leanh::lean_ctor_get(v_toElabInfo_1545_, 0);
                    leanh::lean_dec(v_unused_1602_);
                    v___x_1549_ = v_toElabInfo_1545_;
                    v_isShared_1550_ = v_isSharedCheck_1601_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_stx_1547_);
                    leanh::lean_dec(v_toElabInfo_1545_);
                    v___x_1549_ = leanh::lean_box(0);
                    v_isShared_1550_ = v_isSharedCheck_1601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_stx_1547_);
                v___x_1551_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v___x_1533_, v_stx_1547_);
                if v___x_1551_ == 0 {
                    leanh::lean_del_object(v___x_1549_);
                    leanh::lean_dec(v_stx_1547_);
                    leanh::lean_dec_ref(v_expr_1546_);
                    leanh::lean_dec_ref(v_ci_1535_);
                    v___x_1552_ = leanh::lean_box(0);
                    if v_isShared_1544_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1543_, 0);
                        leanh::lean_ctor_set(v___x_1543_, 0, v___x_1552_);
                        v___x_1554_ = v___x_1543_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1555_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
                        v___x_1554_ = v_reuseFailAlloc_1555_;
                        state = 3;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v_expr_1546_) == 4 {
                        v_toCommandContextInfo_1556_ = leanh::lean_ctor_get(v_ci_1535_, 0);
                        leanh::lean_inc_ref(v_toCommandContextInfo_1556_);
                        leanh::lean_dec_ref(v_ci_1535_);
                        v_declName_1557_ = leanh::lean_ctor_get(v_expr_1546_, 0);
                        leanh::lean_inc_n(v_declName_1557_, 2);
                        leanh::lean_dec_ref_known(v_expr_1546_, 2);
                        v_env_1558_ = leanh::lean_ctor_get(v_toCommandContextInfo_1556_, 0);
                        leanh::lean_inc_ref(v_env_1558_);
                        leanh::lean_dec_ref(v_toCommandContextInfo_1556_);
                        v___x_1559_ = l_Lean_findInternalDocString_x3f(
                            v_env_1558_,
                            v_declName_1557_,
                            v___x_1534_,
                        );
                        if leanh::lean_obj_tag(v___x_1559_) == 0 {
                            leanh::lean_del_object(v___x_1543_);
                            v_a_1560_ = leanh::lean_ctor_get(v___x_1559_, 0);
                            v_isSharedCheck_1579_ =
                                (!leanh::lean_is_exclusive(v___x_1559_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v___x_1562_ = v___x_1559_;
                                v_isShared_1563_ = v_isSharedCheck_1579_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1560_);
                                leanh::lean_dec(v___x_1559_);
                                v___x_1562_ = leanh::lean_box(0);
                                v_isShared_1563_ = v_isSharedCheck_1579_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_declName_1557_);
                            leanh::lean_dec(v_stx_1547_);
                            v_a_1580_ = leanh::lean_ctor_get(v___x_1559_, 0);
                            v_isSharedCheck_1596_ =
                                (!leanh::lean_is_exclusive(v___x_1559_)) as u8;
                            if v_isSharedCheck_1596_ == 0 {
                                v___x_1582_ = v___x_1559_;
                                v_isShared_1583_ = v_isSharedCheck_1596_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1580_);
                                leanh::lean_dec(v___x_1559_);
                                v___x_1582_ = leanh::lean_box(0);
                                v_isShared_1583_ = v_isSharedCheck_1596_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1549_);
                        leanh::lean_dec(v_stx_1547_);
                        leanh::lean_dec_ref(v_expr_1546_);
                        leanh::lean_dec_ref(v_ci_1535_);
                        v___x_1597_ = leanh::lean_box(0);
                        if v_isShared_1544_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1543_, 0);
                            leanh::lean_ctor_set(v___x_1543_, 0, v___x_1597_);
                            v___x_1599_ = v___x_1543_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1600_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                            v___x_1599_ = v_reuseFailAlloc_1600_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1554_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_1560_) == 0 {
                    leanh::lean_dec(v_declName_1557_);
                    leanh::lean_del_object(v___x_1549_);
                    leanh::lean_dec(v_stx_1547_);
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_a_1560_, 1);
                    if v___x_1551_ == 0 {
                        leanh::lean_dec(v_declName_1557_);
                        leanh::lean_del_object(v___x_1549_);
                        leanh::lean_dec(v_stx_1547_);
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_1562_);
                        v___x_1569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1);
                        v___x_1570_ = 0;
                        v___x_1571_ = l_Lean_MessageData_ofConstName(v_declName_1557_, v___x_1570_);
                        if v_isShared_1550_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1549_, 7);
                            leanh::lean_ctor_set(v___x_1549_, 1, v___x_1571_);
                            leanh::lean_ctor_set(v___x_1549_, 0, v___x_1569_);
                            v___x_1573_ = v___x_1549_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1578_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1569_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1571_);
                            v___x_1573_ = v_reuseFailAlloc_1578_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_1565_ = leanh::lean_box(0);
                if v_isShared_1563_ == 0 {
                    leanh::lean_ctor_set(v___x_1562_, 0, v___x_1565_);
                    v___x_1567_ = v___x_1562_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                    v___x_1567_ = v_reuseFailAlloc_1568_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1567_;
            }
            7 => {
                v___x_1574_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3);
                v___x_1575_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                leanh::lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                v___x_1576_ = l_Lean_Linter_linter_tactic_docsOnAlt;
                v___x_1577_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___x_1576_, v_stx_1547_, v___x_1575_, v___y_1538_, v___y_1539_);
                leanh::lean_dec(v_stx_1547_);
                return v___x_1577_;
            }
            8 => {
                v_ref_1584_ = leanh::lean_ctor_get(v___y_1538_, 7);
                v___x_1585_ = lean_io_error_to_string(v_a_1580_);
                if v_isShared_1544_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1543_, 3);
                    leanh::lean_ctor_set(v___x_1543_, 0, v___x_1585_);
                    v___x_1587_ = v___x_1543_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1585_);
                    v___x_1587_ = v_reuseFailAlloc_1595_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1588_ = l_Lean_MessageData_ofFormat(v___x_1587_);
                leanh::lean_inc(v_ref_1584_);
                if v_isShared_1550_ == 0 {
                    leanh::lean_ctor_set(v___x_1549_, 1, v___x_1588_);
                    leanh::lean_ctor_set(v___x_1549_, 0, v_ref_1584_);
                    v___x_1590_ = v___x_1549_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_ref_1584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1588_);
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1583_ == 0 {
                    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1590_);
                    v___x_1592_ = v___x_1582_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1592_;
            }
            12 => {
                return v___x_1599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___boxed(
    mut v___x_1606_: *mut leanh::LeanObject,
    mut v___x_1607_: *mut leanh::LeanObject,
    mut v_ci_1608_: *mut leanh::LeanObject,
    mut v_info_1609_: *mut leanh::LeanObject,
    mut v_x_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9243__boxed_1614_: u8 = 0;
    let mut v_res_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9243__boxed_1614_ = (leanh::lean_unbox(v___x_1607_) as u8);
    v_res_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1(v___x_1606_, v___x_9243__boxed_1614_, v_ci_1608_, v_info_1609_, v_x_1610_, v___y_1611_, v___y_1612_);
    leanh::lean_dec(v___y_1612_);
    leanh::lean_dec_ref(v___y_1611_);
    leanh::lean_dec_ref(v_x_1610_);
    leanh::lean_dec_ref(v___x_1606_);
    return v_res_1615_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(
    mut v___x_1616_: u8,
    mut v_x_1617_: *mut leanh::LeanObject,
    mut v_x_1618_: *mut leanh::LeanObject,
    mut v_x_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = leanh::lean_box((v___x_1616_) as usize);
    v___x_1624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
    return v___x_1624_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed(
    mut v___x_1625_: *mut leanh::LeanObject,
    mut v_x_1626_: *mut leanh::LeanObject,
    mut v_x_1627_: *mut leanh::LeanObject,
    mut v_x_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9384__boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9384__boxed_1632_ = (leanh::lean_unbox(v___x_1625_) as u8);
    v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(v___x_9384__boxed_1632_, v_x_1626_, v_x_1627_, v_x_1628_, v___y_1629_, v___y_1630_);
    leanh::lean_dec(v___y_1630_);
    leanh::lean_dec_ref(v___y_1629_);
    leanh::lean_dec_ref(v_x_1628_);
    leanh::lean_dec_ref(v_x_1627_);
    leanh::lean_dec_ref(v_x_1626_);
    return v_res_1633_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0(
    mut v_postNode_1634_: *mut leanh::LeanObject,
    mut v_ci_1635_: *mut leanh::LeanObject,
    mut v_i_1636_: *mut leanh::LeanObject,
    mut v_cs_1637_: *mut leanh::LeanObject,
    mut v_x_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1640_);
    leanh::lean_inc_ref(v___y_1639_);
    v___x_1642_ = leanh::lean_apply_6(
        v_postNode_1634_,
        v_ci_1635_,
        v_i_1636_,
        v_cs_1637_,
        v___y_1639_,
        v___y_1640_,
        leanh::lean_box(0),
    );
    return v___x_1642_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0___boxed(
    mut v_postNode_1643_: *mut leanh::LeanObject,
    mut v_ci_1644_: *mut leanh::LeanObject,
    mut v_i_1645_: *mut leanh::LeanObject,
    mut v_cs_1646_: *mut leanh::LeanObject,
    mut v_x_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0(v_postNode_1643_, v_ci_1644_, v_i_1645_, v_cs_1646_, v_x_1647_, v___y_1648_, v___y_1649_);
    leanh::lean_dec(v___y_1649_);
    leanh::lean_dec_ref(v___y_1648_);
    leanh::lean_dec(v_x_1647_);
    return v_res_1651_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1652_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(
    mut v_msg_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v_toFunctor_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___f_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7707__overap_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_unused_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1692_: u8 = 0;
    let mut v_unused_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1659_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0);
                v___x_1660_ = l_StateRefT_x27_instMonad___redArg(v___x_1659_);
                v_toApplicative_1661_ = leanh::lean_ctor_get(v___x_1660_, 0);
                v_isSharedCheck_1692_ = (!leanh::lean_is_exclusive(v___x_1660_)) as u8;
                if v_isSharedCheck_1692_ == 0 {
                    v_unused_1693_ = leanh::lean_ctor_get(v___x_1660_, 1);
                    leanh::lean_dec(v_unused_1693_);
                    v___x_1663_ = v___x_1660_;
                    v_isShared_1664_ = v_isSharedCheck_1692_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1661_);
                    leanh::lean_dec(v___x_1660_);
                    v___x_1663_ = leanh::lean_box(0);
                    v_isShared_1664_ = v_isSharedCheck_1692_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1665_ = leanh::lean_ctor_get(v_toApplicative_1661_, 0);
                v_toSeq_1666_ = leanh::lean_ctor_get(v_toApplicative_1661_, 2);
                v_toSeqLeft_1667_ = leanh::lean_ctor_get(v_toApplicative_1661_, 3);
                v_toSeqRight_1668_ = leanh::lean_ctor_get(v_toApplicative_1661_, 4);
                v_isSharedCheck_1690_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1661_)) as u8;
                if v_isSharedCheck_1690_ == 0 {
                    v_unused_1691_ = leanh::lean_ctor_get(v_toApplicative_1661_, 1);
                    leanh::lean_dec(v_unused_1691_);
                    v___x_1670_ = v_toApplicative_1661_;
                    v_isShared_1671_ = v_isSharedCheck_1690_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1668_);
                    leanh::lean_inc(v_toSeqLeft_1667_);
                    leanh::lean_inc(v_toSeq_1666_);
                    leanh::lean_inc(v_toFunctor_1665_);
                    leanh::lean_dec(v_toApplicative_1661_);
                    v___x_1670_ = leanh::lean_box(0);
                    v_isShared_1671_ = v_isSharedCheck_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1672_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1;
                v___f_1673_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1665_);
                v___f_1674_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1674_, 0, v_toFunctor_1665_);
                v___f_1675_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1675_, 0, v_toFunctor_1665_);
                v___x_1676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1676_, 0, v___f_1674_);
                leanh::lean_ctor_set(v___x_1676_, 1, v___f_1675_);
                v___f_1677_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1677_, 0, v_toSeqRight_1668_);
                v___f_1678_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1678_, 0, v_toSeqLeft_1667_);
                v___f_1679_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1679_, 0, v_toSeq_1666_);
                if v_isShared_1671_ == 0 {
                    leanh::lean_ctor_set(v___x_1670_, 4, v___f_1677_);
                    leanh::lean_ctor_set(v___x_1670_, 3, v___f_1678_);
                    leanh::lean_ctor_set(v___x_1670_, 2, v___f_1679_);
                    leanh::lean_ctor_set(v___x_1670_, 1, v___f_1672_);
                    leanh::lean_ctor_set(v___x_1670_, 0, v___x_1676_);
                    v___x_1681_ = v___x_1670_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___f_1672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 2, v___f_1679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 3, v___f_1678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 4, v___f_1677_);
                    v___x_1681_ = v_reuseFailAlloc_1689_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1664_ == 0 {
                    leanh::lean_ctor_set(v___x_1663_, 1, v___f_1673_);
                    leanh::lean_ctor_set(v___x_1663_, 0, v___x_1681_);
                    v___x_1683_ = v___x_1663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___f_1673_);
                    v___x_1683_ = v_reuseFailAlloc_1688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1684_ = leanh::lean_box(0);
                v___x_1685_ = l_instInhabitedOfMonad___redArg(v___x_1683_, v___x_1684_);
                v___x_7707__overap_1686_ = lean_panic_fn_borrowed(v___x_1685_, v_msg_1655_);
                leanh::lean_dec(v___x_1685_);
                leanh::lean_inc(v___y_1657_);
                leanh::lean_inc_ref(v___y_1656_);
                v___x_1687_ = leanh::lean_apply_3(
                    v___x_7707__overap_1686_,
                    v___y_1656_,
                    v___y_1657_,
                    leanh::lean_box(0),
                );
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_msg_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v_msg_1694_, v___y_1695_, v___y_1696_);
    leanh::lean_dec(v___y_1696_);
    leanh::lean_dec_ref(v___y_1695_);
    return v_res_1698_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2;
    v___x_1703_ = leanh::lean_unsigned_to_nat(21);
    v___x_1704_ = leanh::lean_unsigned_to_nat(65);
    v___x_1705_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1;
    v___x_1706_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0;
    v___x_1707_ = l_mkPanicMessageWithDecl(
        v___x_1706_,
        v___x_1705_,
        v___x_1704_,
        v___x_1703_,
        v___x_1702_,
    );
    return v___x_1707_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(
    mut v_preNode_1708_: *mut leanh::LeanObject,
    mut v_postNode_1709_: *mut leanh::LeanObject,
    mut v_x_1710_: *mut leanh::LeanObject,
    mut v_x_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_a_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_unused_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_a_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut v_a_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_a_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut v_unused_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1711_) {
                0 => {
                    v_i_1715_ = leanh::lean_ctor_get(v_x_1711_, 0);
                    leanh::lean_inc_ref(v_i_1715_);
                    v_t_1716_ = leanh::lean_ctor_get(v_x_1711_, 1);
                    leanh::lean_inc_ref(v_t_1716_);
                    leanh::lean_dec_ref_known(v_x_1711_, 2);
                    v___x_1717_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1715_, v_x_1710_);
                    v_x_1710_ = v___x_1717_;
                    v_x_1711_ = v_t_1716_;
                    state = 0;
                    continue;
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_1710_) == 0 {
                        leanh::lean_dec_ref_known(v_x_1711_, 2);
                        leanh::lean_dec_ref(v_postNode_1709_);
                        leanh::lean_dec_ref(v_preNode_1708_);
                        v___x_1719_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3);
                        v___x_1720_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v___x_1719_, v___y_1712_, v___y_1713_);
                        return v___x_1720_;
                    } else {
                        v_i_1721_ = leanh::lean_ctor_get(v_x_1711_, 0);
                        leanh::lean_inc_ref_n(v_i_1721_, 2);
                        v_children_1722_ = leanh::lean_ctor_get(v_x_1711_, 1);
                        leanh::lean_inc_ref_n(v_children_1722_, 2);
                        leanh::lean_dec_ref_known(v_x_1711_, 2);
                        v_val_1723_ = leanh::lean_ctor_get(v_x_1710_, 0);
                        leanh::lean_inc_n(v_val_1723_, 2);
                        leanh::lean_inc_ref(v_preNode_1708_);
                        leanh::lean_inc(v___y_1713_);
                        leanh::lean_inc_ref(v___y_1712_);
                        v___x_1724_ = leanh::lean_apply_6(
                            v_preNode_1708_,
                            v_val_1723_,
                            v_i_1721_,
                            v_children_1722_,
                            v___y_1712_,
                            v___y_1713_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_1724_) == 0 {
                            v_a_1725_ = leanh::lean_ctor_get(v___x_1724_, 0);
                            leanh::lean_inc(v_a_1725_);
                            leanh::lean_dec_ref_known(v___x_1724_, 1);
                            v___x_1726_ = (leanh::lean_unbox(v_a_1725_) as u8);
                            leanh::lean_dec(v_a_1725_);
                            if v___x_1726_ == 0 {
                                leanh::lean_dec_ref(v_preNode_1708_);
                                v_isSharedCheck_1751_ =
                                    (!leanh::lean_is_exclusive(v_x_1710_)) as u8;
                                if v_isSharedCheck_1751_ == 0 {
                                    v_unused_1752_ = leanh::lean_ctor_get(v_x_1710_, 0);
                                    leanh::lean_dec(v_unused_1752_);
                                    v___x_1728_ = v_x_1710_;
                                    v_isShared_1729_ = v_isSharedCheck_1751_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_1710_);
                                    v___x_1728_ = leanh::lean_box(0);
                                    v_isShared_1729_ = v_isSharedCheck_1751_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_1753_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_1710_, v_i_1721_);
                                v___x_1754_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_1722_);
                                v___x_1755_ = leanh::lean_box(0);
                                leanh::lean_inc_ref(v_postNode_1709_);
                                v___x_1756_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_1708_, v_postNode_1709_, v___x_1753_, v___x_1754_, v___x_1755_, v___y_1712_, v___y_1713_);
                                if leanh::lean_obj_tag(v___x_1756_) == 0 {
                                    v_a_1757_ = leanh::lean_ctor_get(v___x_1756_, 0);
                                    leanh::lean_inc(v_a_1757_);
                                    leanh::lean_dec_ref_known(v___x_1756_, 1);
                                    leanh::lean_inc(v___y_1713_);
                                    leanh::lean_inc_ref(v___y_1712_);
                                    v___x_1758_ = leanh::lean_apply_7(
                                        v_postNode_1709_,
                                        v_val_1723_,
                                        v_i_1721_,
                                        v_children_1722_,
                                        v_a_1757_,
                                        v___y_1712_,
                                        v___y_1713_,
                                        leanh::lean_box(0),
                                    );
                                    if leanh::lean_obj_tag(v___x_1758_) == 0 {
                                        v_a_1759_ = leanh::lean_ctor_get(v___x_1758_, 0);
                                        v_isSharedCheck_1767_ =
                                            (!leanh::lean_is_exclusive(v___x_1758_)) as u8;
                                        if v_isSharedCheck_1767_ == 0 {
                                            v___x_1761_ = v___x_1758_;
                                            v_isShared_1762_ = v_isSharedCheck_1767_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1759_);
                                            leanh::lean_dec(v___x_1758_);
                                            v___x_1761_ = leanh::lean_box(0);
                                            v_isShared_1762_ = v_isSharedCheck_1767_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_1768_ = leanh::lean_ctor_get(v___x_1758_, 0);
                                        v_isSharedCheck_1775_ =
                                            (!leanh::lean_is_exclusive(v___x_1758_)) as u8;
                                        if v_isSharedCheck_1775_ == 0 {
                                            v___x_1770_ = v___x_1758_;
                                            v_isShared_1771_ = v_isSharedCheck_1775_;
                                            state = 9;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1768_);
                                            leanh::lean_dec(v___x_1758_);
                                            v___x_1770_ = leanh::lean_box(0);
                                            v_isShared_1771_ = v_isSharedCheck_1775_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_val_1723_);
                                    leanh::lean_dec_ref(v_children_1722_);
                                    leanh::lean_dec_ref(v_i_1721_);
                                    leanh::lean_dec_ref(v_postNode_1709_);
                                    v_a_1776_ = leanh::lean_ctor_get(v___x_1756_, 0);
                                    v_isSharedCheck_1783_ =
                                        (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                                    if v_isSharedCheck_1783_ == 0 {
                                        v___x_1778_ = v___x_1756_;
                                        v_isShared_1779_ = v_isSharedCheck_1783_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1776_);
                                        leanh::lean_dec(v___x_1756_);
                                        v___x_1778_ = leanh::lean_box(0);
                                        v_isShared_1779_ = v_isSharedCheck_1783_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_1723_);
                            leanh::lean_dec_ref(v_children_1722_);
                            leanh::lean_dec_ref(v_i_1721_);
                            leanh::lean_dec_ref_known(v_x_1710_, 1);
                            leanh::lean_dec_ref(v_postNode_1709_);
                            leanh::lean_dec_ref(v_preNode_1708_);
                            v_a_1784_ = leanh::lean_ctor_get(v___x_1724_, 0);
                            v_isSharedCheck_1791_ =
                                (!leanh::lean_is_exclusive(v___x_1724_)) as u8;
                            if v_isSharedCheck_1791_ == 0 {
                                v___x_1786_ = v___x_1724_;
                                v_isShared_1787_ = v_isSharedCheck_1791_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1784_);
                                leanh::lean_dec(v___x_1724_);
                                v___x_1786_ = leanh::lean_box(0);
                                v_isShared_1787_ = v_isSharedCheck_1791_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_1710_);
                    leanh::lean_dec_ref(v_postNode_1709_);
                    leanh::lean_dec_ref(v_preNode_1708_);
                    v_isSharedCheck_1799_ = (!leanh::lean_is_exclusive(v_x_1711_)) as u8;
                    if v_isSharedCheck_1799_ == 0 {
                        v_unused_1800_ = leanh::lean_ctor_get(v_x_1711_, 0);
                        leanh::lean_dec(v_unused_1800_);
                        v___x_1793_ = v_x_1711_;
                        v_isShared_1794_ = v_isSharedCheck_1799_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1711_);
                        v___x_1793_ = leanh::lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1799_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1730_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_1713_);
                leanh::lean_inc_ref(v___y_1712_);
                v___x_1731_ = leanh::lean_apply_7(
                    v_postNode_1709_,
                    v_val_1723_,
                    v_i_1721_,
                    v_children_1722_,
                    v___x_1730_,
                    v___y_1712_,
                    v___y_1713_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1731_) == 0 {
                    v_a_1732_ = leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1742_ = (!leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1742_ == 0 {
                        v___x_1734_ = v___x_1731_;
                        v_isShared_1735_ = v_isSharedCheck_1742_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1732_);
                        leanh::lean_dec(v___x_1731_);
                        v___x_1734_ = leanh::lean_box(0);
                        v_isShared_1735_ = v_isSharedCheck_1742_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1728_);
                    v_a_1743_ = leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1750_ = (!leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1750_ == 0 {
                        v___x_1745_ = v___x_1731_;
                        v_isShared_1746_ = v_isSharedCheck_1750_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1743_);
                        leanh::lean_dec(v___x_1731_);
                        v___x_1745_ = leanh::lean_box(0);
                        v_isShared_1746_ = v_isSharedCheck_1750_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1729_ == 0 {
                    leanh::lean_ctor_set(v___x_1728_, 0, v_a_1732_);
                    v___x_1737_ = v___x_1728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1732_);
                    v___x_1737_ = v_reuseFailAlloc_1741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1735_ == 0 {
                    leanh::lean_ctor_set(v___x_1734_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1734_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1739_;
            }
            5 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1748_;
            }
            7 => {
                v___x_1763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1763_, 0, v_a_1759_);
                if v_isShared_1762_ == 0 {
                    leanh::lean_ctor_set(v___x_1761_, 0, v___x_1763_);
                    v___x_1765_ = v___x_1761_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1765_;
            }
            9 => {
                if v_isShared_1771_ == 0 {
                    v___x_1773_ = v___x_1770_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1774_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
                    v___x_1773_ = v_reuseFailAlloc_1774_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1773_;
            }
            11 => {
                if v_isShared_1779_ == 0 {
                    v___x_1781_ = v___x_1778_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1781_;
            }
            13 => {
                if v_isShared_1787_ == 0 {
                    v___x_1789_ = v___x_1786_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
                    v___x_1789_ = v_reuseFailAlloc_1790_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1789_;
            }
            15 => {
                v___x_1795_ = leanh::lean_box(0);
                if v_isShared_1794_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1793_, 0);
                    leanh::lean_ctor_set(v___x_1793_, 0, v___x_1795_);
                    v___x_1797_ = v___x_1793_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(
    mut v_preNode_1801_: *mut leanh::LeanObject,
    mut v_postNode_1802_: *mut leanh::LeanObject,
    mut v___x_1803_: *mut leanh::LeanObject,
    mut v_x_1804_: *mut leanh::LeanObject,
    mut v_x_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1804_) == 0 {
                    leanh::lean_dec(v___x_1803_);
                    leanh::lean_dec_ref(v_postNode_1802_);
                    leanh::lean_dec_ref(v_preNode_1801_);
                    v___x_1809_ = l_List_reverse___redArg(v_x_1805_);
                    v___x_1810_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1810_, 0, v___x_1809_);
                    return v___x_1810_;
                } else {
                    v_head_1811_ = leanh::lean_ctor_get(v_x_1804_, 0);
                    v_tail_1812_ = leanh::lean_ctor_get(v_x_1804_, 1);
                    v_isSharedCheck_1830_ = (!leanh::lean_is_exclusive(v_x_1804_)) as u8;
                    if v_isSharedCheck_1830_ == 0 {
                        v___x_1814_ = v_x_1804_;
                        v_isShared_1815_ = v_isSharedCheck_1830_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1812_);
                        leanh::lean_inc(v_head_1811_);
                        leanh::lean_dec(v_x_1804_);
                        v___x_1814_ = leanh::lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1830_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_1803_);
                leanh::lean_inc_ref(v_postNode_1802_);
                leanh::lean_inc_ref(v_preNode_1801_);
                v___x_1816_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_1801_, v_postNode_1802_, v___x_1803_, v_head_1811_, v___y_1806_, v___y_1807_);
                if leanh::lean_obj_tag(v___x_1816_) == 0 {
                    v_a_1817_ = leanh::lean_ctor_get(v___x_1816_, 0);
                    leanh::lean_inc(v_a_1817_);
                    leanh::lean_dec_ref_known(v___x_1816_, 1);
                    if v_isShared_1815_ == 0 {
                        leanh::lean_ctor_set(v___x_1814_, 1, v_x_1805_);
                        leanh::lean_ctor_set(v___x_1814_, 0, v_a_1817_);
                        v___x_1819_ = v___x_1814_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1821_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1817_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_x_1805_);
                        v___x_1819_ = v_reuseFailAlloc_1821_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1814_);
                    leanh::lean_dec(v_tail_1812_);
                    leanh::lean_dec(v_x_1805_);
                    leanh::lean_dec(v___x_1803_);
                    leanh::lean_dec_ref(v_postNode_1802_);
                    leanh::lean_dec_ref(v_preNode_1801_);
                    v_a_1822_ = leanh::lean_ctor_get(v___x_1816_, 0);
                    v_isSharedCheck_1829_ = (!leanh::lean_is_exclusive(v___x_1816_)) as u8;
                    if v_isSharedCheck_1829_ == 0 {
                        v___x_1824_ = v___x_1816_;
                        v_isShared_1825_ = v_isSharedCheck_1829_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1822_);
                        leanh::lean_dec(v___x_1816_);
                        v___x_1824_ = leanh::lean_box(0);
                        v_isShared_1825_ = v_isSharedCheck_1829_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_1804_ = v_tail_1812_;
                v_x_1805_ = v___x_1819_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1825_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
                    v___x_1827_ = v_reuseFailAlloc_1828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_preNode_1831_: *mut leanh::LeanObject,
    mut v_postNode_1832_: *mut leanh::LeanObject,
    mut v___x_1833_: *mut leanh::LeanObject,
    mut v_x_1834_: *mut leanh::LeanObject,
    mut v_x_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_1831_, v_postNode_1832_, v___x_1833_, v_x_1834_, v_x_1835_, v___y_1836_, v___y_1837_);
    leanh::lean_dec(v___y_1837_);
    leanh::lean_dec_ref(v___y_1836_);
    return v_res_1839_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___boxed(
    mut v_preNode_1840_: *mut leanh::LeanObject,
    mut v_postNode_1841_: *mut leanh::LeanObject,
    mut v_x_1842_: *mut leanh::LeanObject,
    mut v_x_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_1840_, v_postNode_1841_, v_x_1842_, v_x_1843_, v___y_1844_, v___y_1845_);
    leanh::lean_dec(v___y_1845_);
    leanh::lean_dec_ref(v___y_1844_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(
    mut v_preNode_1848_: *mut leanh::LeanObject,
    mut v_postNode_1849_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1850_: *mut leanh::LeanObject,
    mut v_t_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1864_: u8 = 0;
    let mut v_unused_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1855_ = leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1855_, 0, v_postNode_1849_);
                v___x_1856_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_1848_, v___f_1855_, v_ctx_x3f_1850_, v_t_1851_, v___y_1852_, v___y_1853_);
                if leanh::lean_obj_tag(v___x_1856_) == 0 {
                    v_isSharedCheck_1864_ = (!leanh::lean_is_exclusive(v___x_1856_)) as u8;
                    if v_isSharedCheck_1864_ == 0 {
                        v_unused_1865_ = leanh::lean_ctor_get(v___x_1856_, 0);
                        leanh::lean_dec(v_unused_1865_);
                        v___x_1858_ = v___x_1856_;
                        v_isShared_1859_ = v_isSharedCheck_1864_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1856_);
                        v___x_1858_ = leanh::lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1864_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1866_ = leanh::lean_ctor_get(v___x_1856_, 0);
                    v_isSharedCheck_1873_ = (!leanh::lean_is_exclusive(v___x_1856_)) as u8;
                    if v_isSharedCheck_1873_ == 0 {
                        v___x_1868_ = v___x_1856_;
                        v_isShared_1869_ = v_isSharedCheck_1873_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1866_);
                        leanh::lean_dec(v___x_1856_);
                        v___x_1868_ = leanh::lean_box(0);
                        v_isShared_1869_ = v_isSharedCheck_1873_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1860_ = leanh::lean_box(0);
                if v_isShared_1859_ == 0 {
                    leanh::lean_ctor_set(v___x_1858_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
                    v___x_1862_ = v_reuseFailAlloc_1863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1862_;
            }
            3 => {
                if v_isShared_1869_ == 0 {
                    v___x_1871_ = v___x_1868_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___boxed(
    mut v_preNode_1874_: *mut leanh::LeanObject,
    mut v_postNode_1875_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1876_: *mut leanh::LeanObject,
    mut v_t_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v_preNode_1874_, v_postNode_1875_, v_ctx_x3f_1876_, v_t_1877_, v___y_1878_, v___y_1879_);
    leanh::lean_dec(v___y_1879_);
    leanh::lean_dec_ref(v___y_1878_);
    return v_res_1881_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(
    mut v___x_1882_: u8,
    mut v___x_1883_: *mut leanh::LeanObject,
    mut v_as_1884_: *mut leanh::LeanObject,
    mut v_sz_1885_: usize,
    mut v_i_1886_: usize,
    mut v_b_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1891_ = lean_usize_dec_lt(v_i_1886_, v_sz_1885_);
                if v___x_1891_ == 0 {
                    leanh::lean_dec_ref(v___x_1883_);
                    v___x_1892_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1892_, 0, v_b_1887_);
                    return v___x_1892_;
                } else {
                    v___x_1893_ = leanh::lean_box((v___x_1882_) as usize);
                    v___f_1894_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_1894_, 0, v___x_1893_);
                    v___x_1895_ = leanh::lean_box((v___x_1882_) as usize);
                    leanh::lean_inc_ref(v___x_1883_);
                    v___f_1896_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___boxed as *mut core::ffi::c_void, 8, 2);
                    leanh::lean_closure_set(v___f_1896_, 0, v___x_1883_);
                    leanh::lean_closure_set(v___f_1896_, 1, v___x_1895_);
                    v_a_1897_ = lean_array_uget_borrowed(v_as_1884_, v_i_1886_);
                    v___x_1898_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_1897_);
                    v___x_1899_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v___f_1894_, v___f_1896_, v___x_1898_, v_a_1897_, v___y_1888_, v___y_1889_);
                    if leanh::lean_obj_tag(v___x_1899_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1899_, 1);
                        v___x_1900_ = leanh::lean_box(0);
                        v___x_1901_ = 1usize;
                        v___x_1902_ = lean_usize_add(v_i_1886_, v___x_1901_);
                        v_i_1886_ = v___x_1902_;
                        v_b_1887_ = v___x_1900_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_1883_);
                        return v___x_1899_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___boxed(
    mut v___x_1904_: *mut leanh::LeanObject,
    mut v___x_1905_: *mut leanh::LeanObject,
    mut v_as_1906_: *mut leanh::LeanObject,
    mut v_sz_1907_: *mut leanh::LeanObject,
    mut v_i_1908_: *mut leanh::LeanObject,
    mut v_b_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9824__boxed_1913_: u8 = 0;
    let mut v_sz_boxed_1914_: usize = 0;
    let mut v_i_boxed_1915_: usize = 0;
    let mut v_res_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9824__boxed_1913_ = (leanh::lean_unbox(v___x_1904_) as u8);
    v_sz_boxed_1914_ = leanh::lean_unbox_usize(v_sz_1907_);
    leanh::lean_dec(v_sz_1907_);
    v_i_boxed_1915_ = leanh::lean_unbox_usize(v_i_1908_);
    leanh::lean_dec(v_i_1908_);
    v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v___x_9824__boxed_1913_, v___x_1905_, v_as_1906_, v_sz_boxed_1914_, v_i_boxed_1915_, v_b_1909_, v___y_1910_, v___y_1911_);
    leanh::lean_dec(v___y_1911_);
    leanh::lean_dec_ref(v___y_1910_);
    leanh::lean_dec_ref(v_as_1906_);
    return v_res_1916_;
}
pub unsafe fn _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ =
        l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1;
    v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(
    mut v___f_1921_: *mut leanh::LeanObject,
    mut v___f_1922_: *mut leanh::LeanObject,
    mut v___f_1923_: *mut leanh::LeanObject,
    mut v_stx_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_unused_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1976_: usize = 0;
    let mut v___x_1977_: usize = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_unused_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1928_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v___y_1925_, v___y_1926_);
                v_a_1929_ = leanh::lean_ctor_get(v___x_1928_, 0);
                v_isSharedCheck_1989_ = (!leanh::lean_is_exclusive(v___x_1928_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v___x_1931_ = v___x_1928_;
                    v_isShared_1932_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1929_);
                    leanh::lean_dec(v___x_1928_);
                    v___x_1931_ = leanh::lean_box(0);
                    v_isShared_1932_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1941_ =
                    l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(v_a_1929_);
                leanh::lean_dec(v_a_1929_);
                if v___x_1941_ == 0 {
                    leanh::lean_del_object(v___x_1931_);
                    leanh::lean_dec(v_stx_1924_);
                    leanh::lean_dec_ref(v___f_1923_);
                    leanh::lean_dec_ref(v___f_1922_);
                    leanh::lean_dec_ref(v___f_1921_);
                    v___x_1942_ = leanh::lean_box(0);
                    v___x_1943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1942_);
                    return v___x_1943_;
                } else {
                    leanh::lean_inc(v_stx_1924_);
                    v___x_1944_ = l_Lean_Syntax_find_x3f(v_stx_1924_, v___f_1921_);
                    if leanh::lean_obj_tag(v___x_1944_) == 1 {
                        leanh::lean_del_object(v___x_1931_);
                        leanh::lean_dec(v_stx_1924_);
                        leanh::lean_dec_ref(v___f_1923_);
                        v_val_1945_ = leanh::lean_ctor_get(v___x_1944_, 0);
                        leanh::lean_inc_n(v_val_1945_, 2);
                        leanh::lean_dec_ref_known(v___x_1944_, 1);
                        v___x_1946_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0;
                        v___x_1947_ = l_Lean_Syntax_find_x3f(v_val_1945_, v___x_1946_);
                        if leanh::lean_obj_tag(v___x_1947_) == 0 {
                            leanh::lean_dec(v_val_1945_);
                            leanh::lean_dec_ref(v___f_1922_);
                            state = 4;
                            continue;
                        } else {
                            v_isSharedCheck_1960_ =
                                (!leanh::lean_is_exclusive(v___x_1947_)) as u8;
                            if v_isSharedCheck_1960_ == 0 {
                                v_unused_1961_ = leanh::lean_ctor_get(v___x_1947_, 0);
                                leanh::lean_dec(v_unused_1961_);
                                v___x_1949_ = v___x_1947_;
                                v_isShared_1950_ = v_isSharedCheck_1960_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1947_);
                                v___x_1949_ = leanh::lean_box(0);
                                v_isShared_1950_ = v_isSharedCheck_1960_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1944_);
                        leanh::lean_dec_ref(v___f_1922_);
                        v___x_1962_ = l_Lean_Syntax_find_x3f(v_stx_1924_, v___f_1923_);
                        if leanh::lean_obj_tag(v___x_1962_) == 1 {
                            v_val_1963_ = leanh::lean_ctor_get(v___x_1962_, 0);
                            leanh::lean_inc(v_val_1963_);
                            leanh::lean_dec_ref_known(v___x_1962_, 1);
                            v___x_1964_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1965_ = l_Lean_Syntax_getArg(v_val_1963_, v___x_1964_);
                            v___x_1966_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0;
                            v___x_1967_ = l_Lean_Syntax_find_x3f(v___x_1965_, v___x_1966_);
                            if leanh::lean_obj_tag(v___x_1967_) == 0 {
                                leanh::lean_dec(v_val_1963_);
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_1967_, 1);
                                if v___x_1941_ == 0 {
                                    leanh::lean_dec(v_val_1963_);
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_1931_);
                                    v___x_1968_ = lean_st_ref_get(v___y_1926_);
                                    v_infoState_1969_ = leanh::lean_ctor_get(v___x_1968_, 8);
                                    leanh::lean_inc_ref(v_infoState_1969_);
                                    leanh::lean_dec(v___x_1968_);
                                    v_trees_1970_ =
                                        leanh::lean_ctor_get(v_infoState_1969_, 2);
                                    leanh::lean_inc_ref(v_trees_1970_);
                                    leanh::lean_dec_ref(v_infoState_1969_);
                                    v___x_1971_ = leanh::lean_unsigned_to_nat(4);
                                    v___x_1972_ = l_Lean_Syntax_getArg(v_val_1963_, v___x_1971_);
                                    leanh::lean_dec(v_val_1963_);
                                    v___x_1973_ = l_Lean_Syntax_getArgs(v___x_1972_);
                                    leanh::lean_dec(v___x_1972_);
                                    v___x_1974_ =
                                        l_Lean_PersistentArray_toArray___redArg(v_trees_1970_);
                                    leanh::lean_dec_ref(v_trees_1970_);
                                    v___x_1975_ = leanh::lean_box(0);
                                    v_sz_1976_ = lean_array_size(v___x_1974_);
                                    v___x_1977_ = 0usize;
                                    v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v___x_1941_, v___x_1973_, v___x_1974_, v_sz_1976_, v___x_1977_, v___x_1975_, v___y_1925_, v___y_1926_);
                                    leanh::lean_dec_ref(v___x_1974_);
                                    if leanh::lean_obj_tag(v___x_1978_) == 0 {
                                        v_isSharedCheck_1985_ =
                                            (!leanh::lean_is_exclusive(v___x_1978_)) as u8;
                                        if v_isSharedCheck_1985_ == 0 {
                                            v_unused_1986_ =
                                                leanh::lean_ctor_get(v___x_1978_, 0);
                                            leanh::lean_dec(v_unused_1986_);
                                            v___x_1980_ = v___x_1978_;
                                            v_isShared_1981_ = v_isSharedCheck_1985_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_1978_);
                                            v___x_1980_ = leanh::lean_box(0);
                                            v_isShared_1981_ = v_isSharedCheck_1985_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        return v___x_1978_;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1962_);
                            leanh::lean_del_object(v___x_1931_);
                            v___x_1987_ = leanh::lean_box(0);
                            v___x_1988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1988_, 0, v___x_1987_);
                            return v___x_1988_;
                        }
                    }
                }
            }
            2 => {
                v___x_1934_ = leanh::lean_box(0);
                if v_isShared_1932_ == 0 {
                    leanh::lean_ctor_set(v___x_1931_, 0, v___x_1934_);
                    v___x_1936_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
                    v___x_1936_ = v_reuseFailAlloc_1937_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1936_;
            }
            4 => {
                v___x_1939_ = leanh::lean_box(0);
                v___x_1940_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1940_, 0, v___x_1939_);
                return v___x_1940_;
            }
            5 => {
                if v___x_1941_ == 0 {
                    leanh::lean_del_object(v___x_1949_);
                    leanh::lean_dec(v_val_1945_);
                    leanh::lean_dec_ref(v___f_1922_);
                    state = 4;
                    continue;
                } else {
                    v___x_1951_ = l_Lean_Syntax_find_x3f(v_val_1945_, v___f_1922_);
                    if leanh::lean_obj_tag(v___x_1951_) == 1 {
                        leanh::lean_del_object(v___x_1949_);
                        v_val_1952_ = leanh::lean_ctor_get(v___x_1951_, 0);
                        leanh::lean_inc(v_val_1952_);
                        leanh::lean_dec_ref_known(v___x_1951_, 1);
                        v___x_1953_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2_once), _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2);
                        v___x_1954_ = l_Lean_Linter_linter_tactic_docsOnAlt;
                        v___x_1955_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___x_1954_, v_val_1952_, v___x_1953_, v___y_1925_, v___y_1926_);
                        leanh::lean_dec(v_val_1952_);
                        return v___x_1955_;
                    } else {
                        leanh::lean_dec(v___x_1951_);
                        v___x_1956_ = leanh::lean_box(0);
                        if v_isShared_1950_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1949_, 0);
                            leanh::lean_ctor_set(v___x_1949_, 0, v___x_1956_);
                            v___x_1958_ = v___x_1949_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1959_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
                            v___x_1958_ = v_reuseFailAlloc_1959_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_1958_;
            }
            7 => {
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set(v___x_1980_, 0, v___x_1975_);
                    v___x_1983_ = v___x_1980_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1984_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1975_);
                    v___x_1983_ = v_reuseFailAlloc_1984_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed(
    mut v___f_1990_: *mut leanh::LeanObject,
    mut v___f_1991_: *mut leanh::LeanObject,
    mut v___f_1992_: *mut leanh::LeanObject,
    mut v_stx_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(
        v___f_1990_,
        v___f_1991_,
        v___f_1992_,
        v_stx_1993_,
        v___y_1994_,
        v___y_1995_,
    );
    leanh::lean_dec(v___y_1995_);
    leanh::lean_dec_ref(v___y_1994_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0(
    mut v_o_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_o_2038_, v___y_2040_);
    return v___x_2042_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___boxed(
    mut v_o_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0(v_o_2043_, v___y_2044_, v___y_2045_);
    leanh::lean_dec(v___y_2045_);
    leanh::lean_dec_ref(v___y_2044_);
    return v_res_2047_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8(
    mut v_00_u03b1_2048_: *mut leanh::LeanObject,
    mut v_msg_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v_msg_2049_, v___y_2050_, v___y_2051_);
    return v___x_2053_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b1_2054_: *mut leanh::LeanObject,
    mut v_msg_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8(v_00_u03b1_2054_, v_msg_2055_, v___y_2056_, v___y_2057_);
    leanh::lean_dec(v___y_2057_);
    leanh::lean_dec_ref(v___y_2056_);
    return v_res_2059_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6(
    mut v_00_u03b1_2060_: *mut leanh::LeanObject,
    mut v_preNode_2061_: *mut leanh::LeanObject,
    mut v_postNode_2062_: *mut leanh::LeanObject,
    mut v_x_2063_: *mut leanh::LeanObject,
    mut v_x_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2068_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_2061_, v_postNode_2062_, v_x_2063_, v_x_2064_, v___y_2065_, v___y_2066_);
    return v___x_2068_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___boxed(
    mut v_00_u03b1_2069_: *mut leanh::LeanObject,
    mut v_preNode_2070_: *mut leanh::LeanObject,
    mut v_postNode_2071_: *mut leanh::LeanObject,
    mut v_x_2072_: *mut leanh::LeanObject,
    mut v_x_2073_: *mut leanh::LeanObject,
    mut v___y_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2077_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6(v_00_u03b1_2069_, v_preNode_2070_, v_postNode_2071_, v_x_2072_, v_x_2073_, v___y_2074_, v___y_2075_);
    leanh::lean_dec(v___y_2075_);
    leanh::lean_dec_ref(v___y_2074_);
    return v_res_2077_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7(
    mut v_msgData_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v_msgData_2078_, v___y_2080_);
    return v___x_2082_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___boxed(
    mut v_msgData_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7(v_msgData_2083_, v___y_2084_, v___y_2085_);
    leanh::lean_dec(v___y_2085_);
    leanh::lean_dec_ref(v___y_2084_);
    return v_res_2087_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9(
    mut v_00_u03b1_2088_: *mut leanh::LeanObject,
    mut v_preNode_2089_: *mut leanh::LeanObject,
    mut v_postNode_2090_: *mut leanh::LeanObject,
    mut v___x_2091_: *mut leanh::LeanObject,
    mut v_x_2092_: *mut leanh::LeanObject,
    mut v_x_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_2089_, v_postNode_2090_, v___x_2091_, v_x_2092_, v_x_2093_, v___y_2094_, v___y_2095_);
    return v___x_2097_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03b1_2098_: *mut leanh::LeanObject,
    mut v_preNode_2099_: *mut leanh::LeanObject,
    mut v_postNode_2100_: *mut leanh::LeanObject,
    mut v___x_2101_: *mut leanh::LeanObject,
    mut v_x_2102_: *mut leanh::LeanObject,
    mut v_x_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2107_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9(v_00_u03b1_2098_, v_preNode_2099_, v_postNode_2100_, v___x_2101_, v_x_2102_, v_x_2103_, v___y_2104_, v___y_2105_);
    leanh::lean_dec(v___y_2105_);
    leanh::lean_dec_ref(v___y_2104_);
    return v_res_2107_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt;
    v___x_2110_ = l_Lean_Elab_Command_addLinter(v___x_2109_);
    return v___x_2110_;
}
pub unsafe fn l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2____boxed(
    mut v_a_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2112_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
    return v_res_2112_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_DocsOnAlt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_tactic_docsOnAlt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Linter_linter_tactic_docsOnAlt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_DocsOnAlt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_DocsOnAlt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_DocsOnAlt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_DocsOnAlt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_DocsOnAlt(builtin);
}