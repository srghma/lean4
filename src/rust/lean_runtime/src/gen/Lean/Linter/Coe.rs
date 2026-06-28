// Lean compiler output
// Module: Lean.Linter.Coe
// Imports: Lean.Elab.Command Lean.Server.InfoUtils Lean.Linter.Init Lean.Elab.Term.TermElabM
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_contains___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_elem___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_getRoot;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::l_Lean_ParametricAttribute_getParam_x3f___redArg;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_toList___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
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
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM,
    l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_,
    l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2,
    l_Lean_Option_register___at___00__private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0,
    runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_Environment_header;
use crate::r#gen::Lean::Linter::Deprecated::{
    l_Lean_Linter_deprecatedAttr, l_Lean_Linter_instInhabitedDeprecationEntry_default,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag,
    l_Lean_Linter_linterSetsExt, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, runtime_initialize_Lean_Server_InfoUtils,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 67, 111, 101, 114, 99, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17550368434844301537 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [86, 97, 108, 105, 100, 97, 116, 101, 32, 116, 104, 97, 116, 32, 110, 111, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 99, 111, 101, 114, 99, 105, 111, 110, 115, 32, 97, 114, 101, 32, 117, 115, 101, 100, 46, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 111, 101, 0]};
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13484979753806722408 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8772335467362107925 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5025721139949978778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value:
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
    m_data: [111, 112, 116, 105, 111, 110, 67, 111, 101, 0],
};
static mut l_Lean_Linter_Coe_coercionsBannedInCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3443816031865713090 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_Coe_coercionsBannedInCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value:
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
        105, 110, 115, 116, 67, 111, 101, 83, 117, 98, 97, 114, 114, 97, 121, 65, 114, 114, 97,
        121, 0,
    ],
};
static mut l_Lean_Linter_Coe_coercionsBannedInCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4166408114542578798 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_Coe_coercionsBannedInCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value:
    crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_Coe_coercionsBannedInCore___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_Coe_coercionsBannedInCore: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100,
        105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111,
        112, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2_value:
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
    m_data: [32, 102, 97, 108, 115, 101, 96, 0],
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 116, 116, 114, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11717111273439622741 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [84, 104, 105, 115, 32, 116, 101, 114, 109, 32, 117, 115, 101, 115, 32, 116, 104, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [84, 104, 105, 115, 32, 116, 101, 114, 109, 32, 117, 115, 101, 115, 32, 116, 104, 101, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 98, 97, 110, 110, 101, 100, 32, 105, 110, 32, 76, 101, 97, 110, 39, 115, 32, 99, 111, 114, 101, 32, 108, 105, 98, 114, 97, 114, 121, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 97, 98, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 105, 110, 116, 101, 114, 67, 111, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value) as *mut crate::leanh::LeanObject,10433073528599050961 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject,997197196521451961 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 105, 116, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject,1882184448842950296 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coeLinter___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_Coe_coeLinter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_Coe_coeLinter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coeLinter___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 111, 101, 76, 105, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Linter_Coe_coeLinter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13484979753806722408 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_Coe_coeLinter___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6465750432273363179 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_Coe_coeLinter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Coe_coeLinter___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_Coe_coeLinter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_Coe_coeLinter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Coe_coeLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_;
    v___x_1359_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_;
    v___x_1360_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_;
    v___x_1361_ = l_Lean_Option_register___at___00__private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0(v___x_1358_, v___x_1359_, v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(
    mut v_a_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
    return v_res_1363_;
}
pub unsafe fn l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(
    mut v_toPure_1364_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
    v_name_1367_ = crate::leanh::lean_ctor_get(v___x_1366_, 0);
    v_map_1368_ = crate::leanh::lean_ctor_get(v_____do__lift_1365_, 0);
    v___x_1369_ = 1;
    v___x_1370_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1368_,
            v_name_1367_,
        );
    if crate::leanh::lean_obj_tag(v___x_1370_) == 0 {
        let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1371_ = crate::leanh::lean_box((v___x_1369_) as usize);
        v___x_1372_ =
            crate::leanh::lean_apply_2(v_toPure_1364_, crate::leanh::lean_box(0), v___x_1371_);
        return v___x_1372_;
    } else {
        let mut v_val_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1373_ = crate::leanh::lean_ctor_get(v___x_1370_, 0);
        crate::leanh::lean_inc(v_val_1373_);
        crate::leanh::lean_dec_ref_known(v___x_1370_, 1);
        if crate::leanh::lean_obj_tag(v_val_1373_) == 1 {
            let mut v_v_1374_: u8 = 0;
            let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1374_ = crate::leanh::lean_ctor_get_uint8(v_val_1373_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1373_, 0);
            v___x_1375_ = crate::leanh::lean_box((v_v_1374_) as usize);
            v___x_1376_ =
                crate::leanh::lean_apply_2(v_toPure_1364_, crate::leanh::lean_box(0), v___x_1375_);
            return v___x_1376_;
        } else {
            let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_1373_);
            v___x_1377_ = crate::leanh::lean_box((v___x_1369_) as usize);
            v___x_1378_ =
                crate::leanh::lean_apply_2(v_toPure_1364_, crate::leanh::lean_box(0), v___x_1377_);
            return v___x_1378_;
        }
    }
}
pub unsafe fn l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed(
    mut v_toPure_1379_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1381_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(
        v_toPure_1379_,
        v_____do__lift_1380_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1380_);
    return v_res_1381_;
}
pub unsafe fn l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(
    mut v_inst_1382_: *mut crate::leanh::LeanObject,
    mut v_inst_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1384_ = crate::leanh::lean_ctor_get(v_inst_1382_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1384_);
    v_toBind_1385_ = crate::leanh::lean_ctor_get(v_inst_1382_, 1);
    crate::leanh::lean_inc(v_toBind_1385_);
    crate::leanh::lean_dec_ref(v_inst_1382_);
    v_toPure_1386_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 1);
    crate::leanh::lean_inc(v_toPure_1386_);
    crate::leanh::lean_dec_ref(v_toApplicative_1384_);
    v___f_1387_ = crate::leanh::lean_alloc_closure(
        l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1387_, 0, v_toPure_1386_);
    v___x_1388_ = crate::leanh::lean_apply_4(
        v_toBind_1385_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1383_,
        v___f_1387_,
    );
    return v___x_1388_;
}
pub unsafe fn l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(
    mut v_m_1389_: *mut crate::leanh::LeanObject,
    mut v_inst_1390_: *mut crate::leanh::LeanObject,
    mut v_inst_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ =
        l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(v_inst_1390_, v_inst_1391_);
    return v___x_1392_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(
    mut v___y_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = lean_st_ref_get(v___y_1406_);
    v_env_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
    crate::leanh::lean_inc_ref(v_env_1409_);
    crate::leanh::lean_dec(v___x_1408_);
    v___x_1410_ = l_Lean_Environment_header(v_env_1409_);
    crate::leanh::lean_dec_ref(v_env_1409_);
    v_mainModule_1411_ = crate::leanh::lean_ctor_get(v___x_1410_, 0);
    crate::leanh::lean_inc(v_mainModule_1411_);
    crate::leanh::lean_dec_ref(v___x_1410_);
    v___x_1412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1412_, 0, v_mainModule_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1415_ =
        l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1413_);
    crate::leanh::lean_dec(v___y_1413_);
    return v_res_1415_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ =
        l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1417_);
    return v___x_1419_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1423_ =
        l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_1420_, v___y_1421_);
    crate::leanh::lean_dec(v___y_1421_);
    crate::leanh::lean_dec_ref(v___y_1420_);
    return v_res_1423_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(
    mut v___y_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_st_ref_get(v___y_1424_);
    v_infoState_1427_ = crate::leanh::lean_ctor_get(v___x_1426_, 8);
    crate::leanh::lean_inc_ref(v_infoState_1427_);
    crate::leanh::lean_dec(v___x_1426_);
    v_trees_1428_ = crate::leanh::lean_ctor_get(v_infoState_1427_, 2);
    crate::leanh::lean_inc_ref(v_trees_1428_);
    crate::leanh::lean_dec_ref(v_infoState_1427_);
    v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_trees_1428_);
    return v___x_1429_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1430_);
    crate::leanh::lean_dec(v___y_1430_);
    return v_res_1432_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1434_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(
        v___y_1437_,
        v___y_1438_,
    );
    crate::leanh::lean_dec(v___y_1438_);
    crate::leanh::lean_dec_ref(v___y_1437_);
    return v_res_1440_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0(
    mut v_postNode_1441_: *mut crate::leanh::LeanObject,
    mut v_ci_1442_: *mut crate::leanh::LeanObject,
    mut v_i_1443_: *mut crate::leanh::LeanObject,
    mut v_cs_1444_: *mut crate::leanh::LeanObject,
    mut v_x_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1447_);
    crate::leanh::lean_inc_ref(v___y_1446_);
    v___x_1449_ = crate::leanh::lean_apply_6(
        v_postNode_1441_,
        v_ci_1442_,
        v_i_1443_,
        v_cs_1444_,
        v___y_1446_,
        v___y_1447_,
        crate::leanh::lean_box(0),
    );
    return v___x_1449_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0___boxed(
    mut v_postNode_1450_: *mut crate::leanh::LeanObject,
    mut v_ci_1451_: *mut crate::leanh::LeanObject,
    mut v_i_1452_: *mut crate::leanh::LeanObject,
    mut v_cs_1453_: *mut crate::leanh::LeanObject,
    mut v_x_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ =
        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0(
            v_postNode_1450_,
            v_ci_1451_,
            v_i_1452_,
            v_cs_1453_,
            v_x_1454_,
            v___y_1455_,
            v___y_1456_,
        );
    crate::leanh::lean_dec(v___y_1456_);
    crate::leanh::lean_dec_ref(v___y_1455_);
    crate::leanh::lean_dec(v_x_1454_);
    return v_res_1458_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1459_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(
    mut v_msg_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1471_: u8 = 0;
    let mut v_toFunctor_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___f_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8503__overap_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v_unused_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_unused_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0);
                v___x_1467_ = l_StateRefT_x27_instMonad___redArg(v___x_1466_);
                v_toApplicative_1468_ = crate::leanh::lean_ctor_get(v___x_1467_, 0);
                v_isSharedCheck_1499_ = (!crate::leanh::lean_is_exclusive(v___x_1467_)) as u8;
                if v_isSharedCheck_1499_ == 0 {
                    v_unused_1500_ = crate::leanh::lean_ctor_get(v___x_1467_, 1);
                    crate::leanh::lean_dec(v_unused_1500_);
                    v___x_1470_ = v___x_1467_;
                    v_isShared_1471_ = v_isSharedCheck_1499_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1468_);
                    crate::leanh::lean_dec(v___x_1467_);
                    v___x_1470_ = crate::leanh::lean_box(0);
                    v_isShared_1471_ = v_isSharedCheck_1499_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1472_ = crate::leanh::lean_ctor_get(v_toApplicative_1468_, 0);
                v_toSeq_1473_ = crate::leanh::lean_ctor_get(v_toApplicative_1468_, 2);
                v_toSeqLeft_1474_ = crate::leanh::lean_ctor_get(v_toApplicative_1468_, 3);
                v_toSeqRight_1475_ = crate::leanh::lean_ctor_get(v_toApplicative_1468_, 4);
                v_isSharedCheck_1497_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1468_)) as u8;
                if v_isSharedCheck_1497_ == 0 {
                    v_unused_1498_ = crate::leanh::lean_ctor_get(v_toApplicative_1468_, 1);
                    crate::leanh::lean_dec(v_unused_1498_);
                    v___x_1477_ = v_toApplicative_1468_;
                    v_isShared_1478_ = v_isSharedCheck_1497_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1475_);
                    crate::leanh::lean_inc(v_toSeqLeft_1474_);
                    crate::leanh::lean_inc(v_toSeq_1473_);
                    crate::leanh::lean_inc(v_toFunctor_1472_);
                    crate::leanh::lean_dec(v_toApplicative_1468_);
                    v___x_1477_ = crate::leanh::lean_box(0);
                    v_isShared_1478_ = v_isSharedCheck_1497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1479_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1;
                v___f_1480_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1472_);
                v___f_1481_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1481_, 0, v_toFunctor_1472_);
                v___f_1482_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1482_, 0, v_toFunctor_1472_);
                v___x_1483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1483_, 0, v___f_1481_);
                crate::leanh::lean_ctor_set(v___x_1483_, 1, v___f_1482_);
                v___f_1484_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1484_, 0, v_toSeqRight_1475_);
                v___f_1485_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1485_, 0, v_toSeqLeft_1474_);
                v___f_1486_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1486_, 0, v_toSeq_1473_);
                if v_isShared_1478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1477_, 4, v___f_1484_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 3, v___f_1485_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 2, v___f_1486_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 1, v___f_1479_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1483_);
                    v___x_1488_ = v___x_1477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___f_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 2, v___f_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 3, v___f_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 4, v___f_1484_);
                    v___x_1488_ = v_reuseFailAlloc_1496_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1470_, 1, v___f_1480_);
                    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1488_);
                    v___x_1490_ = v___x_1470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___f_1480_);
                    v___x_1490_ = v_reuseFailAlloc_1495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1491_ = crate::leanh::lean_box(0);
                v___x_1492_ = l_instInhabitedOfMonad___redArg(v___x_1490_, v___x_1491_);
                v___x_8503__overap_1493_ = lean_panic_fn_borrowed(v___x_1492_, v_msg_1462_);
                crate::leanh::lean_dec(v___x_1492_);
                crate::leanh::lean_inc(v___y_1464_);
                crate::leanh::lean_inc_ref(v___y_1463_);
                v___x_1494_ = crate::leanh::lean_apply_3(
                    v___x_8503__overap_1493_,
                    v___y_1463_,
                    v___y_1464_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_msg_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
    mut v___y_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1505_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v_msg_1501_, v___y_1502_, v___y_1503_);
    crate::leanh::lean_dec(v___y_1503_);
    crate::leanh::lean_dec_ref(v___y_1502_);
    return v_res_1505_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2;
    v___x_1510_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1511_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_1512_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1;
    v___x_1513_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0;
    v___x_1514_ = l_mkPanicMessageWithDecl(
        v___x_1513_,
        v___x_1512_,
        v___x_1511_,
        v___x_1510_,
        v___x_1509_,
    );
    return v___x_1514_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(
    mut v_preNode_1515_: *mut crate::leanh::LeanObject,
    mut v_postNode_1516_: *mut crate::leanh::LeanObject,
    mut v_x_1517_: *mut crate::leanh::LeanObject,
    mut v_x_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut v_a_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut v_unused_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_a_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_a_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_a_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1518_) {
                0 => {
                    v_i_1522_ = crate::leanh::lean_ctor_get(v_x_1518_, 0);
                    crate::leanh::lean_inc_ref(v_i_1522_);
                    v_t_1523_ = crate::leanh::lean_ctor_get(v_x_1518_, 1);
                    crate::leanh::lean_inc_ref(v_t_1523_);
                    crate::leanh::lean_dec_ref_known(v_x_1518_, 2);
                    v___x_1524_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1522_, v_x_1517_);
                    v_x_1517_ = v___x_1524_;
                    v_x_1518_ = v_t_1523_;
                    state = 0;
                    continue;
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_1517_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_1518_, 2);
                        crate::leanh::lean_dec_ref(v_postNode_1516_);
                        crate::leanh::lean_dec_ref(v_preNode_1515_);
                        v___x_1526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3);
                        v___x_1527_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v___x_1526_, v___y_1519_, v___y_1520_);
                        return v___x_1527_;
                    } else {
                        v_i_1528_ = crate::leanh::lean_ctor_get(v_x_1518_, 0);
                        crate::leanh::lean_inc_ref_n(v_i_1528_, 2);
                        v_children_1529_ = crate::leanh::lean_ctor_get(v_x_1518_, 1);
                        crate::leanh::lean_inc_ref_n(v_children_1529_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_1518_, 2);
                        v_val_1530_ = crate::leanh::lean_ctor_get(v_x_1517_, 0);
                        crate::leanh::lean_inc_n(v_val_1530_, 2);
                        crate::leanh::lean_inc_ref(v_preNode_1515_);
                        crate::leanh::lean_inc(v___y_1520_);
                        crate::leanh::lean_inc_ref(v___y_1519_);
                        v___x_1531_ = crate::leanh::lean_apply_6(
                            v_preNode_1515_,
                            v_val_1530_,
                            v_i_1528_,
                            v_children_1529_,
                            v___y_1519_,
                            v___y_1520_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                            v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                            crate::leanh::lean_inc(v_a_1532_);
                            crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                            v___x_1533_ = (crate::leanh::lean_unbox(v_a_1532_) as u8);
                            crate::leanh::lean_dec(v_a_1532_);
                            if v___x_1533_ == 0 {
                                crate::leanh::lean_dec_ref(v_preNode_1515_);
                                v_isSharedCheck_1558_ =
                                    (!crate::leanh::lean_is_exclusive(v_x_1517_)) as u8;
                                if v_isSharedCheck_1558_ == 0 {
                                    v_unused_1559_ = crate::leanh::lean_ctor_get(v_x_1517_, 0);
                                    crate::leanh::lean_dec(v_unused_1559_);
                                    v___x_1535_ = v_x_1517_;
                                    v_isShared_1536_ = v_isSharedCheck_1558_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_x_1517_);
                                    v___x_1535_ = crate::leanh::lean_box(0);
                                    v_isShared_1536_ = v_isSharedCheck_1558_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_1560_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_1517_, v_i_1528_);
                                v___x_1561_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_1529_);
                                v___x_1562_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_ref(v_postNode_1516_);
                                v___x_1563_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_1515_, v_postNode_1516_, v___x_1560_, v___x_1561_, v___x_1562_, v___y_1519_, v___y_1520_);
                                if crate::leanh::lean_obj_tag(v___x_1563_) == 0 {
                                    v_a_1564_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                    crate::leanh::lean_inc(v_a_1564_);
                                    crate::leanh::lean_dec_ref_known(v___x_1563_, 1);
                                    crate::leanh::lean_inc(v___y_1520_);
                                    crate::leanh::lean_inc_ref(v___y_1519_);
                                    v___x_1565_ = crate::leanh::lean_apply_7(
                                        v_postNode_1516_,
                                        v_val_1530_,
                                        v_i_1528_,
                                        v_children_1529_,
                                        v_a_1564_,
                                        v___y_1519_,
                                        v___y_1520_,
                                        crate::leanh::lean_box(0),
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1565_) == 0 {
                                        v_a_1566_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                                        v_isSharedCheck_1574_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1565_)) as u8;
                                        if v_isSharedCheck_1574_ == 0 {
                                            v___x_1568_ = v___x_1565_;
                                            v_isShared_1569_ = v_isSharedCheck_1574_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1566_);
                                            crate::leanh::lean_dec(v___x_1565_);
                                            v___x_1568_ = crate::leanh::lean_box(0);
                                            v_isShared_1569_ = v_isSharedCheck_1574_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_1575_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                                        v_isSharedCheck_1582_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1565_)) as u8;
                                        if v_isSharedCheck_1582_ == 0 {
                                            v___x_1577_ = v___x_1565_;
                                            v_isShared_1578_ = v_isSharedCheck_1582_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1575_);
                                            crate::leanh::lean_dec(v___x_1565_);
                                            v___x_1577_ = crate::leanh::lean_box(0);
                                            v_isShared_1578_ = v_isSharedCheck_1582_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_1530_);
                                    crate::leanh::lean_dec_ref(v_children_1529_);
                                    crate::leanh::lean_dec_ref(v_i_1528_);
                                    crate::leanh::lean_dec_ref(v_postNode_1516_);
                                    v_a_1583_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                    v_isSharedCheck_1590_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1563_)) as u8;
                                    if v_isSharedCheck_1590_ == 0 {
                                        v___x_1585_ = v___x_1563_;
                                        v_isShared_1586_ = v_isSharedCheck_1590_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1583_);
                                        crate::leanh::lean_dec(v___x_1563_);
                                        v___x_1585_ = crate::leanh::lean_box(0);
                                        v_isShared_1586_ = v_isSharedCheck_1590_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_1530_);
                            crate::leanh::lean_dec_ref(v_children_1529_);
                            crate::leanh::lean_dec_ref_known(v_x_1517_, 1);
                            crate::leanh::lean_dec_ref(v_i_1528_);
                            crate::leanh::lean_dec_ref(v_postNode_1516_);
                            crate::leanh::lean_dec_ref(v_preNode_1515_);
                            v_a_1591_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                            v_isSharedCheck_1598_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1531_)) as u8;
                            if v_isSharedCheck_1598_ == 0 {
                                v___x_1593_ = v___x_1531_;
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1591_);
                                crate::leanh::lean_dec(v___x_1531_);
                                v___x_1593_ = crate::leanh::lean_box(0);
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_1517_);
                    crate::leanh::lean_dec_ref(v_postNode_1516_);
                    crate::leanh::lean_dec_ref(v_preNode_1515_);
                    v_isSharedCheck_1606_ = (!crate::leanh::lean_is_exclusive(v_x_1518_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v_unused_1607_ = crate::leanh::lean_ctor_get(v_x_1518_, 0);
                        crate::leanh::lean_dec(v_unused_1607_);
                        v___x_1600_ = v_x_1518_;
                        v_isShared_1601_ = v_isSharedCheck_1606_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1518_);
                        v___x_1600_ = crate::leanh::lean_box(0);
                        v_isShared_1601_ = v_isSharedCheck_1606_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1537_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_1520_);
                crate::leanh::lean_inc_ref(v___y_1519_);
                v___x_1538_ = crate::leanh::lean_apply_7(
                    v_postNode_1516_,
                    v_val_1530_,
                    v_i_1528_,
                    v_children_1529_,
                    v___x_1537_,
                    v___y_1519_,
                    v___y_1520_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1538_) == 0 {
                    v_a_1539_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    v_isSharedCheck_1549_ = (!crate::leanh::lean_is_exclusive(v___x_1538_)) as u8;
                    if v_isSharedCheck_1549_ == 0 {
                        v___x_1541_ = v___x_1538_;
                        v_isShared_1542_ = v_isSharedCheck_1549_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1539_);
                        crate::leanh::lean_dec(v___x_1538_);
                        v___x_1541_ = crate::leanh::lean_box(0);
                        v_isShared_1542_ = v_isSharedCheck_1549_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1535_);
                    v_a_1550_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    v_isSharedCheck_1557_ = (!crate::leanh::lean_is_exclusive(v___x_1538_)) as u8;
                    if v_isSharedCheck_1557_ == 0 {
                        v___x_1552_ = v___x_1538_;
                        v_isShared_1553_ = v_isSharedCheck_1557_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1550_);
                        crate::leanh::lean_dec(v___x_1538_);
                        v___x_1552_ = crate::leanh::lean_box(0);
                        v_isShared_1553_ = v_isSharedCheck_1557_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1535_, 0, v_a_1539_);
                    v___x_1544_ = v___x_1535_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1548_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1544_);
                    v___x_1546_ = v___x_1541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
                    v___x_1546_ = v_reuseFailAlloc_1547_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1546_;
            }
            5 => {
                if v_isShared_1553_ == 0 {
                    v___x_1555_ = v___x_1552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
                    v___x_1555_ = v_reuseFailAlloc_1556_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1555_;
            }
            7 => {
                v___x_1570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1570_, 0, v_a_1566_);
                if v_isShared_1569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1568_, 0, v___x_1570_);
                    v___x_1572_ = v___x_1568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
                    v___x_1572_ = v_reuseFailAlloc_1573_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1572_;
            }
            9 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1580_;
            }
            11 => {
                if v_isShared_1586_ == 0 {
                    v___x_1588_ = v___x_1585_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1588_;
            }
            13 => {
                if v_isShared_1594_ == 0 {
                    v___x_1596_ = v___x_1593_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1596_;
            }
            15 => {
                v___x_1602_ = crate::leanh::lean_box(0);
                if v_isShared_1601_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1600_, 0);
                    crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1602_);
                    v___x_1604_ = v___x_1600_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(
    mut v_preNode_1608_: *mut crate::leanh::LeanObject,
    mut v_postNode_1609_: *mut crate::leanh::LeanObject,
    mut v___x_1610_: *mut crate::leanh::LeanObject,
    mut v_x_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1632_: u8 = 0;
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1611_) == 0 {
                    crate::leanh::lean_dec(v___x_1610_);
                    crate::leanh::lean_dec_ref(v_postNode_1609_);
                    crate::leanh::lean_dec_ref(v_preNode_1608_);
                    v___x_1616_ = l_List_reverse___redArg(v_x_1612_);
                    v___x_1617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
                    return v___x_1617_;
                } else {
                    v_head_1618_ = crate::leanh::lean_ctor_get(v_x_1611_, 0);
                    v_tail_1619_ = crate::leanh::lean_ctor_get(v_x_1611_, 1);
                    v_isSharedCheck_1637_ = (!crate::leanh::lean_is_exclusive(v_x_1611_)) as u8;
                    if v_isSharedCheck_1637_ == 0 {
                        v___x_1621_ = v_x_1611_;
                        v_isShared_1622_ = v_isSharedCheck_1637_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1619_);
                        crate::leanh::lean_inc(v_head_1618_);
                        crate::leanh::lean_dec(v_x_1611_);
                        v___x_1621_ = crate::leanh::lean_box(0);
                        v_isShared_1622_ = v_isSharedCheck_1637_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_1610_);
                crate::leanh::lean_inc_ref(v_postNode_1609_);
                crate::leanh::lean_inc_ref(v_preNode_1608_);
                v___x_1623_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_1608_, v_postNode_1609_, v___x_1610_, v_head_1618_, v___y_1613_, v___y_1614_);
                if crate::leanh::lean_obj_tag(v___x_1623_) == 0 {
                    v_a_1624_ = crate::leanh::lean_ctor_get(v___x_1623_, 0);
                    crate::leanh::lean_inc(v_a_1624_);
                    crate::leanh::lean_dec_ref_known(v___x_1623_, 1);
                    if v_isShared_1622_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1621_, 1, v_x_1612_);
                        crate::leanh::lean_ctor_set(v___x_1621_, 0, v_a_1624_);
                        v___x_1626_ = v___x_1621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1624_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_x_1612_);
                        v___x_1626_ = v_reuseFailAlloc_1628_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1621_);
                    crate::leanh::lean_dec(v_tail_1619_);
                    crate::leanh::lean_dec(v_x_1612_);
                    crate::leanh::lean_dec(v___x_1610_);
                    crate::leanh::lean_dec_ref(v_postNode_1609_);
                    crate::leanh::lean_dec_ref(v_preNode_1608_);
                    v_a_1629_ = crate::leanh::lean_ctor_get(v___x_1623_, 0);
                    v_isSharedCheck_1636_ = (!crate::leanh::lean_is_exclusive(v___x_1623_)) as u8;
                    if v_isSharedCheck_1636_ == 0 {
                        v___x_1631_ = v___x_1623_;
                        v_isShared_1632_ = v_isSharedCheck_1636_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1629_);
                        crate::leanh::lean_dec(v___x_1623_);
                        v___x_1631_ = crate::leanh::lean_box(0);
                        v_isShared_1632_ = v_isSharedCheck_1636_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_1611_ = v_tail_1619_;
                v_x_1612_ = v___x_1626_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1632_ == 0 {
                    v___x_1634_ = v___x_1631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
                    v___x_1634_ = v_reuseFailAlloc_1635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg___boxed(
    mut v_preNode_1638_: *mut crate::leanh::LeanObject,
    mut v_postNode_1639_: *mut crate::leanh::LeanObject,
    mut v___x_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_1638_, v_postNode_1639_, v___x_1640_, v_x_1641_, v_x_1642_, v___y_1643_, v___y_1644_);
    crate::leanh::lean_dec(v___y_1644_);
    crate::leanh::lean_dec_ref(v___y_1643_);
    return v_res_1646_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___boxed(
    mut v_preNode_1647_: *mut crate::leanh::LeanObject,
    mut v_postNode_1648_: *mut crate::leanh::LeanObject,
    mut v_x_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_1647_, v_postNode_1648_, v_x_1649_, v_x_1650_, v___y_1651_, v___y_1652_);
    crate::leanh::lean_dec(v___y_1652_);
    crate::leanh::lean_dec_ref(v___y_1651_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
    mut v_preNode_1655_: *mut crate::leanh::LeanObject,
    mut v_postNode_1656_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1657_: *mut crate::leanh::LeanObject,
    mut v_t_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v_unused_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1662_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1662_, 0, v_postNode_1656_);
                v___x_1663_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_1655_, v___f_1662_, v_ctx_x3f_1657_, v_t_1658_, v___y_1659_, v___y_1660_);
                if crate::leanh::lean_obj_tag(v___x_1663_) == 0 {
                    v_isSharedCheck_1671_ = (!crate::leanh::lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_1671_ == 0 {
                        v_unused_1672_ = crate::leanh::lean_ctor_get(v___x_1663_, 0);
                        crate::leanh::lean_dec(v_unused_1672_);
                        v___x_1665_ = v___x_1663_;
                        v_isShared_1666_ = v_isSharedCheck_1671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1663_);
                        v___x_1665_ = crate::leanh::lean_box(0);
                        v_isShared_1666_ = v_isSharedCheck_1671_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1673_ = crate::leanh::lean_ctor_get(v___x_1663_, 0);
                    v_isSharedCheck_1680_ = (!crate::leanh::lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_1680_ == 0 {
                        v___x_1675_ = v___x_1663_;
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1673_);
                        crate::leanh::lean_dec(v___x_1663_);
                        v___x_1675_ = crate::leanh::lean_box(0);
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1667_ = crate::leanh::lean_box(0);
                if v_isShared_1666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1667_);
                    v___x_1669_ = v___x_1665_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
                    v___x_1669_ = v_reuseFailAlloc_1670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1669_;
            }
            3 => {
                if v_isShared_1676_ == 0 {
                    v___x_1678_ = v___x_1675_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
                    v___x_1678_ = v_reuseFailAlloc_1679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(
    mut v_preNode_1681_: *mut crate::leanh::LeanObject,
    mut v_postNode_1682_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1683_: *mut crate::leanh::LeanObject,
    mut v_t_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
        v_preNode_1681_,
        v_postNode_1682_,
        v_ctx_x3f_1683_,
        v_t_1684_,
        v___y_1685_,
        v___y_1686_,
    );
    crate::leanh::lean_dec(v___y_1686_);
    crate::leanh::lean_dec_ref(v___y_1685_);
    return v_res_1688_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1689_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_1691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1693_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1694_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1694_, 0, v___x_1693_);
    crate::leanh::lean_ctor_set(v___x_1694_, 1, v___x_1693_);
    crate::leanh::lean_ctor_set(v___x_1694_, 2, v___x_1693_);
    crate::leanh::lean_ctor_set(v___x_1694_, 3, v___x_1693_);
    crate::leanh::lean_ctor_set(v___x_1694_, 4, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 5, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 6, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 7, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 8, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 9, v___x_1692_);
    return v___x_1694_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1696_ = lean_mk_empty_array_with_capacity(v___x_1695_);
    v___x_1697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = 5usize;
    v___x_1699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1700_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1701_ = lean_mk_empty_array_with_capacity(v___x_1700_);
    v___x_1702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_1703_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1703_, 0, v___x_1702_);
    crate::leanh::lean_ctor_set(v___x_1703_, 1, v___x_1701_);
    crate::leanh::lean_ctor_set(v___x_1703_, 2, v___x_1699_);
    crate::leanh::lean_ctor_set(v___x_1703_, 3, v___x_1699_);
    crate::leanh::lean_ctor_set_usize(v___x_1703_, 4, v___x_1698_);
    return v___x_1703_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = crate::leanh::lean_box(1);
    v___x_1705_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_1706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1707_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1707_, 0, v___x_1706_);
    crate::leanh::lean_ctor_set(v___x_1707_, 1, v___x_1705_);
    crate::leanh::lean_ctor_set(v___x_1707_, 2, v___x_1704_);
    return v___x_1707_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(
    mut v_msgData_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = lean_st_ref_get(v___y_1709_);
    v_env_1712_ = crate::leanh::lean_ctor_get(v___x_1711_, 0);
    crate::leanh::lean_inc_ref(v_env_1712_);
    crate::leanh::lean_dec(v___x_1711_);
    v___x_1713_ = lean_st_ref_get(v___y_1709_);
    v_scopes_1714_ = crate::leanh::lean_ctor_get(v___x_1713_, 2);
    crate::leanh::lean_inc(v_scopes_1714_);
    crate::leanh::lean_dec(v___x_1713_);
    v___x_1715_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1716_ = l_List_head_x21___redArg(v___x_1715_, v_scopes_1714_);
    crate::leanh::lean_dec(v_scopes_1714_);
    v_opts_1717_ = crate::leanh::lean_ctor_get(v___x_1716_, 1);
    crate::leanh::lean_inc_ref(v_opts_1717_);
    crate::leanh::lean_dec(v___x_1716_);
    v___x_1718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2);
    v___x_1719_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5);
    v___x_1720_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1720_, 0, v_env_1712_);
    crate::leanh::lean_ctor_set(v___x_1720_, 1, v___x_1718_);
    crate::leanh::lean_ctor_set(v___x_1720_, 2, v___x_1719_);
    crate::leanh::lean_ctor_set(v___x_1720_, 3, v_opts_1717_);
    v___x_1721_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    crate::leanh::lean_ctor_set(v___x_1721_, 1, v_msgData_1708_);
    v___x_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msgData_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v_msgData_1723_, v___y_1724_);
    crate::leanh::lean_dec(v___y_1724_);
    return v_res_1726_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0(
    mut v___y_1728_: u8,
    mut v_suppressElabErrors_1729_: u8,
    mut v_x_1730_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1730_) == 1 {
        let mut v_pre_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1731_ = crate::leanh::lean_ctor_get(v_x_1730_, 0);
        if crate::leanh::lean_obj_tag(v_pre_1731_) == 0 {
            let mut v_str_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1734_: u8 = 0;
            v_str_1732_ = crate::leanh::lean_ctor_get(v_x_1730_, 1);
            v___x_1733_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0;
            v___x_1734_ = lean_string_dec_eq(v_str_1732_, v___x_1733_);
            if v___x_1734_ == 0 {
                return v___y_1728_;
            } else {
                return v_suppressElabErrors_1729_;
            }
        } else {
            return v___y_1728_;
        }
    } else {
        return v___y_1728_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___boxed(
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_10723__boxed_1738_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1739_: u8 = 0;
    let mut v_res_1740_: u8 = 0;
    let mut v_r_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_10723__boxed_1738_ = (crate::leanh::lean_unbox(v___y_1735_) as u8);
    v_suppressElabErrors_boxed_1739_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1736_) as u8);
    v_res_1740_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0(v___y_10723__boxed_1738_, v_suppressElabErrors_boxed_1739_, v_x_1737_);
    crate::leanh::lean_dec(v_x_1737_);
    v_r_1741_ = crate::leanh::lean_box((v_res_1740_) as usize);
    return v_r_1741_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(
    mut v_ref_1743_: *mut crate::leanh::LeanObject,
    mut v_msgData_1744_: *mut crate::leanh::LeanObject,
    mut v_severity_1745_: u8,
    mut v_isSilent_1746_: u8,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1751_: u8 = 0;
    let mut v___y_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: u8 = 0;
    let mut v___y_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_a_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_a_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v___y_1814_: u8 = 0;
    let mut v___y_1815_: u8 = 0;
    let mut v___y_1816_: u8 = 0;
    let mut v___y_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v___y_1842_: u8 = 0;
    let mut v___y_1843_: u8 = 0;
    let mut v___y_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1845_: u8 = 0;
    let mut v___y_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___y_1851_: u8 = 0;
    let mut v___y_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v___x_1867_: u8 = 0;
    let mut v___y_1869_: u8 = 0;
    let mut v___y_1870_: u8 = 0;
    let mut v___y_1871_: u8 = 0;
    let mut v___y_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1867_ = 2;
                v___x_1885_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1745_, v___x_1867_);
                if v___x_1885_ == 0 {
                    v___y_1873_ = v___x_1885_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1744_);
                    v___x_1886_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1744_);
                    v___y_1873_ = v___x_1886_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1759_ = l_Lean_Elab_Command_getScope___redArg(v___y_1758_);
                if crate::leanh::lean_obj_tag(v___x_1759_) == 0 {
                    v_a_1760_ = crate::leanh::lean_ctor_get(v___x_1759_, 0);
                    crate::leanh::lean_inc(v_a_1760_);
                    crate::leanh::lean_dec_ref_known(v___x_1759_, 1);
                    v___x_1761_ = l_Lean_Elab_Command_getScope___redArg(v___y_1758_);
                    if crate::leanh::lean_obj_tag(v___x_1761_) == 0 {
                        v_a_1762_ = crate::leanh::lean_ctor_get(v___x_1761_, 0);
                        v_isSharedCheck_1796_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1761_)) as u8;
                        if v_isSharedCheck_1796_ == 0 {
                            v___x_1764_ = v___x_1761_;
                            v_isShared_1765_ = v_isSharedCheck_1796_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1762_);
                            crate::leanh::lean_dec(v___x_1761_);
                            v___x_1764_ = crate::leanh::lean_box(0);
                            v_isShared_1765_ = v_isSharedCheck_1796_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1760_);
                        crate::leanh::lean_dec_ref(v___y_1757_);
                        crate::leanh::lean_dec(v___y_1756_);
                        crate::leanh::lean_dec_ref(v___y_1752_);
                        v_a_1797_ = crate::leanh::lean_ctor_get(v___x_1761_, 0);
                        v_isSharedCheck_1804_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1761_)) as u8;
                        if v_isSharedCheck_1804_ == 0 {
                            v___x_1799_ = v___x_1761_;
                            v_isShared_1800_ = v_isSharedCheck_1804_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1797_);
                            crate::leanh::lean_dec(v___x_1761_);
                            v___x_1799_ = crate::leanh::lean_box(0);
                            v_isShared_1800_ = v_isSharedCheck_1804_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1757_);
                    crate::leanh::lean_dec(v___y_1756_);
                    crate::leanh::lean_dec_ref(v___y_1752_);
                    v_a_1805_ = crate::leanh::lean_ctor_get(v___x_1759_, 0);
                    v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v___x_1759_)) as u8;
                    if v_isSharedCheck_1812_ == 0 {
                        v___x_1807_ = v___x_1759_;
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1805_);
                        crate::leanh::lean_dec(v___x_1759_);
                        v___x_1807_ = crate::leanh::lean_box(0);
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1766_ = lean_st_ref_take(v___y_1758_);
                v_currNamespace_1767_ = crate::leanh::lean_ctor_get(v_a_1760_, 2);
                crate::leanh::lean_inc(v_currNamespace_1767_);
                crate::leanh::lean_dec(v_a_1760_);
                v_openDecls_1768_ = crate::leanh::lean_ctor_get(v_a_1762_, 3);
                crate::leanh::lean_inc(v_openDecls_1768_);
                crate::leanh::lean_dec(v_a_1762_);
                v_env_1769_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                v_messages_1770_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                v_scopes_1771_ = crate::leanh::lean_ctor_get(v___x_1766_, 2);
                v_usedQuotCtxts_1772_ = crate::leanh::lean_ctor_get(v___x_1766_, 3);
                v_nextMacroScope_1773_ = crate::leanh::lean_ctor_get(v___x_1766_, 4);
                v_maxRecDepth_1774_ = crate::leanh::lean_ctor_get(v___x_1766_, 5);
                v_ngen_1775_ = crate::leanh::lean_ctor_get(v___x_1766_, 6);
                v_auxDeclNGen_1776_ = crate::leanh::lean_ctor_get(v___x_1766_, 7);
                v_infoState_1777_ = crate::leanh::lean_ctor_get(v___x_1766_, 8);
                v_traceState_1778_ = crate::leanh::lean_ctor_get(v___x_1766_, 9);
                v_snapshotTasks_1779_ = crate::leanh::lean_ctor_get(v___x_1766_, 10);
                v_isSharedCheck_1795_ = (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1781_ = v___x_1766_;
                    v_isShared_1782_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1779_);
                    crate::leanh::lean_inc(v_traceState_1778_);
                    crate::leanh::lean_inc(v_infoState_1777_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1776_);
                    crate::leanh::lean_inc(v_ngen_1775_);
                    crate::leanh::lean_inc(v_maxRecDepth_1774_);
                    crate::leanh::lean_inc(v_nextMacroScope_1773_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1772_);
                    crate::leanh::lean_inc(v_scopes_1771_);
                    crate::leanh::lean_inc(v_messages_1770_);
                    crate::leanh::lean_inc(v_env_1769_);
                    crate::leanh::lean_dec(v___x_1766_);
                    v___x_1781_ = crate::leanh::lean_box(0);
                    v_isShared_1782_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1783_, 0, v_currNamespace_1767_);
                crate::leanh::lean_ctor_set(v___x_1783_, 1, v_openDecls_1768_);
                v___x_1784_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1783_);
                crate::leanh::lean_ctor_set(v___x_1784_, 1, v___y_1752_);
                crate::leanh::lean_inc_ref(v___y_1755_);
                crate::leanh::lean_inc_ref(v___y_1753_);
                v___x_1785_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1785_, 0, v___y_1753_);
                crate::leanh::lean_ctor_set(v___x_1785_, 1, v___y_1757_);
                crate::leanh::lean_ctor_set(v___x_1785_, 2, v___y_1756_);
                crate::leanh::lean_ctor_set(v___x_1785_, 3, v___y_1755_);
                crate::leanh::lean_ctor_set(v___x_1785_, 4, v___x_1784_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1785_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1751_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1785_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1754_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1785_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1746_,
                );
                v___x_1786_ = l_Lean_MessageLog_add(v___x_1785_, v_messages_1770_);
                if v_isShared_1782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1781_, 1, v___x_1786_);
                    v___x_1788_ = v___x_1781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_env_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_scopes_1771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_usedQuotCtxts_1772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_nextMacroScope_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 5, v_maxRecDepth_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 6, v_ngen_1775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 7, v_auxDeclNGen_1776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 8, v_infoState_1777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 9, v_traceState_1778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 10, v_snapshotTasks_1779_);
                    v___x_1788_ = v_reuseFailAlloc_1794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1789_ = lean_st_ref_set(v___y_1758_, v___x_1788_);
                v___x_1790_ = crate::leanh::lean_box(0);
                if v_isShared_1765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1764_, 0, v___x_1790_);
                    v___x_1792_ = v___x_1764_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1792_;
            }
            6 => {
                if v_isShared_1800_ == 0 {
                    v___x_1802_ = v___x_1799_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1802_;
            }
            8 => {
                if v_isShared_1808_ == 0 {
                    v___x_1810_ = v___x_1807_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1810_;
            }
            10 => {
                v_fileName_1819_ = crate::leanh::lean_ctor_get(v___y_1747_, 0);
                v_fileMap_1820_ = crate::leanh::lean_ctor_get(v___y_1747_, 1);
                v_suppressElabErrors_1821_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1747_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_1822_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1744_,
                    );
                v___x_1823_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v___x_1822_, v___y_1748_);
                v_a_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                v_isSharedCheck_1840_ = (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                if v_isSharedCheck_1840_ == 0 {
                    v___x_1826_ = v___x_1823_;
                    v_isShared_1827_ = v_isSharedCheck_1840_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1824_);
                    crate::leanh::lean_dec(v___x_1823_);
                    v___x_1826_ = crate::leanh::lean_box(0);
                    v_isShared_1827_ = v_isSharedCheck_1840_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1820_, 2);
                v___x_1828_ = l_Lean_FileMap_toPosition(v_fileMap_1820_, v___y_1817_);
                crate::leanh::lean_dec(v___y_1817_);
                v___x_1829_ = l_Lean_FileMap_toPosition(v_fileMap_1820_, v___y_1818_);
                crate::leanh::lean_dec(v___y_1818_);
                v___x_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1829_);
                v___x_1831_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0;
                if v_suppressElabErrors_1821_ == 0 {
                    crate::leanh::lean_del_object(v___x_1826_);
                    v___y_1751_ = v___y_1815_;
                    v___y_1752_ = v_a_1824_;
                    v___y_1753_ = v_fileName_1819_;
                    v___y_1754_ = v___y_1816_;
                    v___y_1755_ = v___x_1831_;
                    v___y_1756_ = v___x_1830_;
                    v___y_1757_ = v___x_1828_;
                    v___y_1758_ = v___y_1748_;
                    state = 1;
                    continue;
                } else {
                    v___x_1832_ = crate::leanh::lean_box((v___y_1814_) as usize);
                    v___x_1833_ = crate::leanh::lean_box((v_suppressElabErrors_1821_) as usize);
                    v___f_1834_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1834_, 0, v___x_1832_);
                    crate::leanh::lean_closure_set(v___f_1834_, 1, v___x_1833_);
                    crate::leanh::lean_inc(v_a_1824_);
                    v___x_1835_ = l_Lean_MessageData_hasTag(v___f_1834_, v_a_1824_);
                    if v___x_1835_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1830_, 1);
                        crate::leanh::lean_dec_ref(v___x_1828_);
                        crate::leanh::lean_dec(v_a_1824_);
                        v___x_1836_ = crate::leanh::lean_box(0);
                        if v_isShared_1827_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1836_);
                            v___x_1838_ = v___x_1826_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1839_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
                            v___x_1838_ = v_reuseFailAlloc_1839_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1826_);
                        v___y_1751_ = v___y_1815_;
                        v___y_1752_ = v_a_1824_;
                        v___y_1753_ = v_fileName_1819_;
                        v___y_1754_ = v___y_1816_;
                        v___y_1755_ = v___x_1831_;
                        v___y_1756_ = v___x_1830_;
                        v___y_1757_ = v___x_1828_;
                        v___y_1758_ = v___y_1748_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1838_;
            }
            13 => {
                v___x_1847_ = l_Lean_Syntax_getTailPos_x3f(v___y_1844_, v___y_1843_);
                crate::leanh::lean_dec(v___y_1844_);
                if crate::leanh::lean_obj_tag(v___x_1847_) == 0 {
                    crate::leanh::lean_inc(v___y_1846_);
                    v___y_1814_ = v___y_1842_;
                    v___y_1815_ = v___y_1843_;
                    v___y_1816_ = v___y_1845_;
                    v___y_1817_ = v___y_1846_;
                    v___y_1818_ = v___y_1846_;
                    state = 10;
                    continue;
                } else {
                    v_val_1848_ = crate::leanh::lean_ctor_get(v___x_1847_, 0);
                    crate::leanh::lean_inc(v_val_1848_);
                    crate::leanh::lean_dec_ref_known(v___x_1847_, 1);
                    v___y_1814_ = v___y_1842_;
                    v___y_1815_ = v___y_1843_;
                    v___y_1816_ = v___y_1845_;
                    v___y_1817_ = v___y_1846_;
                    v___y_1818_ = v_val_1848_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1853_ = l_Lean_Elab_Command_getRef___redArg(v___y_1747_);
                if crate::leanh::lean_obj_tag(v___x_1853_) == 0 {
                    v_a_1854_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                    crate::leanh::lean_inc(v_a_1854_);
                    crate::leanh::lean_dec_ref_known(v___x_1853_, 1);
                    v_ref_1855_ = l_Lean_replaceRef(v_ref_1743_, v_a_1854_);
                    crate::leanh::lean_dec(v_a_1854_);
                    v___x_1856_ = l_Lean_Syntax_getPos_x3f(v_ref_1855_, v___y_1851_);
                    if crate::leanh::lean_obj_tag(v___x_1856_) == 0 {
                        v___x_1857_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_1842_ = v___y_1850_;
                        v___y_1843_ = v___y_1851_;
                        v___y_1844_ = v_ref_1855_;
                        v___y_1845_ = v___y_1852_;
                        v___y_1846_ = v___x_1857_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1858_ = crate::leanh::lean_ctor_get(v___x_1856_, 0);
                        crate::leanh::lean_inc(v_val_1858_);
                        crate::leanh::lean_dec_ref_known(v___x_1856_, 1);
                        v___y_1842_ = v___y_1850_;
                        v___y_1843_ = v___y_1851_;
                        v___y_1844_ = v_ref_1855_;
                        v___y_1845_ = v___y_1852_;
                        v___y_1846_ = v_val_1858_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1744_);
                    v_a_1859_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                    v_isSharedCheck_1866_ = (!crate::leanh::lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1861_ = v___x_1853_;
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1859_);
                        crate::leanh::lean_dec(v___x_1853_);
                        v___x_1861_ = crate::leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1862_ == 0 {
                    v___x_1864_ = v___x_1861_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1864_;
            }
            17 => {
                if v___y_1871_ == 0 {
                    v___y_1850_ = v___y_1869_;
                    v___y_1851_ = v___y_1870_;
                    v___y_1852_ = v_severity_1745_;
                    state = 14;
                    continue;
                } else {
                    v___y_1850_ = v___y_1869_;
                    v___y_1851_ = v___y_1870_;
                    v___y_1852_ = v___x_1867_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1873_ == 0 {
                    v___x_1874_ = lean_st_ref_get(v___y_1748_);
                    v_scopes_1875_ = crate::leanh::lean_ctor_get(v___x_1874_, 2);
                    crate::leanh::lean_inc(v_scopes_1875_);
                    crate::leanh::lean_dec(v___x_1874_);
                    v___x_1876_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1877_ = l_List_head_x21___redArg(v___x_1876_, v_scopes_1875_);
                    crate::leanh::lean_dec(v_scopes_1875_);
                    v_opts_1878_ = crate::leanh::lean_ctor_get(v___x_1877_, 1);
                    crate::leanh::lean_inc_ref(v_opts_1878_);
                    crate::leanh::lean_dec(v___x_1877_);
                    v___x_1879_ = 1;
                    v___x_1880_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1745_, v___x_1879_);
                    if v___x_1880_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_1878_);
                        v___y_1869_ = v___y_1873_;
                        v___y_1870_ = v___y_1873_;
                        v___y_1871_ = v___x_1880_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1881_ = l_Lean_warningAsError;
                        v___x_1882_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(v_opts_1878_, v___x_1881_);
                        crate::leanh::lean_dec_ref(v_opts_1878_);
                        v___y_1869_ = v___y_1873_;
                        v___y_1870_ = v___y_1873_;
                        v___y_1871_ = v___x_1882_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1744_);
                    v___x_1883_ = crate::leanh::lean_box(0);
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    return v___x_1884_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(
    mut v_ref_1887_: *mut crate::leanh::LeanObject,
    mut v_msgData_1888_: *mut crate::leanh::LeanObject,
    mut v_severity_1889_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1894_: u8 = 0;
    let mut v_isSilent_boxed_1895_: u8 = 0;
    let mut v_res_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1894_ = (crate::leanh::lean_unbox(v_severity_1889_) as u8);
    v_isSilent_boxed_1895_ = (crate::leanh::lean_unbox(v_isSilent_1890_) as u8);
    v_res_1896_ =
        l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(
            v_ref_1887_,
            v_msgData_1888_,
            v_severity_boxed_1894_,
            v_isSilent_boxed_1895_,
            v___y_1891_,
            v___y_1892_,
        );
    crate::leanh::lean_dec(v___y_1892_);
    crate::leanh::lean_dec_ref(v___y_1891_);
    crate::leanh::lean_dec(v_ref_1887_);
    return v_res_1896_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(
    mut v_ref_1897_: *mut crate::leanh::LeanObject,
    mut v_msgData_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = 1;
    v___x_1903_ = 0;
    v___x_1904_ =
        l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(
            v_ref_1897_,
            v_msgData_1898_,
            v___x_1902_,
            v___x_1903_,
            v___y_1899_,
            v___y_1900_,
        );
    return v___x_1904_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(
    mut v_ref_1905_: *mut crate::leanh::LeanObject,
    mut v_msgData_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(
        v_ref_1905_,
        v_msgData_1906_,
        v___y_1907_,
        v___y_1908_,
    );
    crate::leanh::lean_dec(v___y_1908_);
    crate::leanh::lean_dec_ref(v___y_1907_);
    crate::leanh::lean_dec(v_ref_1905_);
    return v_res_1910_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0;
    v___x_1913_ = l_Lean_stringToMessageData(v___x_1912_);
    return v___x_1913_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2;
    v___x_1916_ = l_Lean_stringToMessageData(v___x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(
    mut v_linterOption_1917_: *mut crate::leanh::LeanObject,
    mut v_stx_1918_: *mut crate::leanh::LeanObject,
    mut v_msg_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1923_ = crate::leanh::lean_ctor_get(v_linterOption_1917_, 0);
                v_isSharedCheck_1940_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_1917_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v_unused_1941_ = crate::leanh::lean_ctor_get(v_linterOption_1917_, 1);
                    crate::leanh::lean_dec(v_unused_1941_);
                    v___x_1925_ = v_linterOption_1917_;
                    v_isShared_1926_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1923_);
                    crate::leanh::lean_dec(v_linterOption_1917_);
                    v___x_1925_ = crate::leanh::lean_box(0);
                    v_isShared_1926_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1);
                crate::leanh::lean_inc(v_name_1923_);
                v___x_1928_ = l_Lean_MessageData_ofName(v_name_1923_);
                if v_isShared_1926_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1925_, 7);
                    crate::leanh::lean_ctor_set(v___x_1925_, 1, v___x_1928_);
                    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1927_);
                    v___x_1930_ = v___x_1925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1928_);
                    v___x_1930_ = v_reuseFailAlloc_1939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1931_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3);
                v___x_1932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1932_, 0, v___x_1930_);
                crate::leanh::lean_ctor_set(v___x_1932_, 1, v___x_1931_);
                v_disable_1933_ = l_Lean_MessageData_note(v___x_1932_);
                v___x_1934_ = l_Lean_Linter_linterMessageTag;
                v___x_1935_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1935_, 0, v_msg_1919_);
                crate::leanh::lean_ctor_set(v___x_1935_, 1, v_disable_1933_);
                v___x_1936_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                crate::leanh::lean_ctor_set(v___x_1936_, 1, v___x_1935_);
                v___x_1937_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1937_, 0, v_name_1923_);
                crate::leanh::lean_ctor_set(v___x_1937_, 1, v___x_1936_);
                v___x_1938_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(
                    v_stx_1918_,
                    v___x_1937_,
                    v___y_1920_,
                    v___y_1921_,
                );
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(
    mut v_linterOption_1942_: *mut crate::leanh::LeanObject,
    mut v_stx_1943_: *mut crate::leanh::LeanObject,
    mut v_msg_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(
        v_linterOption_1942_,
        v_stx_1943_,
        v_msg_1944_,
        v___y_1945_,
        v___y_1946_,
    );
    crate::leanh::lean_dec(v___y_1946_);
    crate::leanh::lean_dec_ref(v___y_1945_);
    crate::leanh::lean_dec(v_stx_1943_);
    return v_res_1948_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2;
    v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4;
    v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7;
    v___x_1963_ = l_Lean_stringToMessageData(v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9;
    v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(
    mut v___x_1984_: u8,
    mut v_i_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1987_: *mut crate::leanh::LeanObject,
    mut v_b_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v_stx_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1987_) == 0 {
                    v___x_1992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1992_, 0, v_b_1988_);
                    return v___x_1992_;
                } else {
                    v_head_1993_ = crate::leanh::lean_ctor_get(v_as_x27_1987_, 0);
                    v_tail_1994_ = crate::leanh::lean_ctor_get(v_as_x27_1987_, 1);
                    v___x_1995_ = crate::leanh::lean_box(0);
                    v___x_1996_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
                    v___x_2017_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6;
                    v___x_2029_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13;
                    v___x_2030_ = lean_name_eq(v_a_1986_, v___x_2029_);
                    if v___x_2030_ == 0 {
                        v___x_2031_ = l_Lean_Name_getRoot(v_a_1986_);
                        v___x_2032_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19;
                        v___x_2033_ = l_List_elem___redArg(v___x_2017_, v___x_2031_, v___x_2032_);
                        v___y_2019_ = v___x_2033_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2019_ = v___x_2030_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___x_1984_ == 0 {
                    v_as_x27_1987_ = v_tail_1994_;
                    v_b_1988_ = v___x_1995_;
                    state = 0;
                    continue;
                } else {
                    v___x_2001_ = lean_st_ref_get(v___y_1999_);
                    v_env_2002_ = crate::leanh::lean_ctor_get(v___x_2001_, 0);
                    crate::leanh::lean_inc_ref(v_env_2002_);
                    crate::leanh::lean_dec(v___x_2001_);
                    v___x_2003_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
                    v___x_2004_ = l_Lean_Linter_deprecatedAttr;
                    crate::leanh::lean_inc(v_head_1993_);
                    v___x_2005_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                        v___x_2003_,
                        v___x_2004_,
                        v_env_2002_,
                        v_head_1993_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2005_) == 1 {
                        crate::leanh::lean_dec_ref_known(v___x_2005_, 1);
                        v_stx_2006_ = crate::leanh::lean_ctor_get(v_i_1985_, 0);
                        v___x_2007_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1;
                        v___x_2008_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3);
                        crate::leanh::lean_inc(v_head_1993_);
                        v___x_2009_ = l_Lean_MessageData_ofConstName(v_head_1993_, v___x_1984_);
                        v___x_2010_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2008_);
                        crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
                        v___x_2011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5);
                        v___x_2012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2010_);
                        crate::leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
                        v___x_2013_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2013_, 0, v___x_2007_);
                        crate::leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
                        v___x_2014_ =
                            l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(
                                v___x_1996_,
                                v_stx_2006_,
                                v___x_2013_,
                                v___y_1998_,
                                v___y_1999_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2014_, 1);
                            v_as_x27_1987_ = v_tail_1994_;
                            v_b_1988_ = v___x_1995_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2014_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2005_);
                        v_as_x27_1987_ = v_tail_1994_;
                        v_b_1988_ = v___x_1995_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_2019_ == 0 {
                    v___y_1998_ = v___y_1989_;
                    v___y_1999_ = v___y_1990_;
                    state = 1;
                    continue;
                } else {
                    v___x_2020_ = l_Lean_Linter_Coe_coercionsBannedInCore;
                    crate::leanh::lean_inc(v_head_1993_);
                    v___x_2021_ = l_Array_contains___redArg(v___x_2017_, v___x_2020_, v_head_1993_);
                    if v___x_2021_ == 0 {
                        v___y_1998_ = v___y_1989_;
                        v___y_1999_ = v___y_1990_;
                        state = 1;
                        continue;
                    } else {
                        v_stx_2022_ = crate::leanh::lean_ctor_get(v_i_1985_, 0);
                        v___x_2023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8);
                        crate::leanh::lean_inc(v_head_1993_);
                        v___x_2024_ = l_Lean_MessageData_ofName(v_head_1993_);
                        v___x_2025_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2023_);
                        crate::leanh::lean_ctor_set(v___x_2025_, 1, v___x_2024_);
                        v___x_2026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10);
                        v___x_2027_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2025_);
                        crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2026_);
                        v___x_2028_ =
                            l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(
                                v_stx_2022_,
                                v___x_2027_,
                                v___y_1989_,
                                v___y_1990_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2028_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2028_, 1);
                            v___y_1998_ = v___y_1989_;
                            v___y_1999_ = v___y_1990_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2028_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___boxed(
    mut v___x_2034_: *mut crate::leanh::LeanObject,
    mut v_i_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2037_: *mut crate::leanh::LeanObject,
    mut v_b_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11139__boxed_2042_: u8 = 0;
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11139__boxed_2042_ = (crate::leanh::lean_unbox(v___x_2034_) as u8);
    v_res_2043_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(
        v___x_11139__boxed_2042_,
        v_i_2035_,
        v_a_2036_,
        v_as_x27_2037_,
        v_b_2038_,
        v___y_2039_,
        v___y_2040_,
    );
    crate::leanh::lean_dec(v___y_2040_);
    crate::leanh::lean_dec_ref(v___y_2039_);
    crate::leanh::lean_dec(v_as_x27_2037_);
    crate::leanh::lean_dec(v_a_2036_);
    crate::leanh::lean_dec_ref(v_i_2035_);
    return v_res_2043_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1(
    mut v___x_2044_: *mut crate::leanh::LeanObject,
    mut v___x_2045_: u8,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v___x_2047_: *mut crate::leanh::LeanObject,
    mut v___x_2048_: u8,
    mut v_x_2049_: *mut crate::leanh::LeanObject,
    mut v_info_2050_: *mut crate::leanh::LeanObject,
    mut v_x_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v_value_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_2050_) == 10 {
                    v_i_2055_ = crate::leanh::lean_ctor_get(v_info_2050_, 0);
                    v_isSharedCheck_2084_ = (!crate::leanh::lean_is_exclusive(v_info_2050_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v___x_2057_ = v_info_2050_;
                        v_isShared_2058_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_2055_);
                        crate::leanh::lean_dec(v_info_2050_);
                        v___x_2057_ = crate::leanh::lean_box(0);
                        v_isShared_2058_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_2050_);
                    v___x_2085_ = crate::leanh::lean_box((v___x_2048_) as usize);
                    v___x_2086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                    return v___x_2086_;
                }
            }
            1 => {
                v_value_2059_ = crate::leanh::lean_ctor_get(v_i_2055_, 1);
                v___x_2060_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_value_2059_,
                    v___x_2044_,
                );
                if crate::leanh::lean_obj_tag(v___x_2060_) == 1 {
                    crate::leanh::lean_del_object(v___x_2057_);
                    v_val_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                    crate::leanh::lean_inc(v_val_2061_);
                    crate::leanh::lean_dec_ref_known(v___x_2060_, 1);
                    v___x_2062_ =
                        l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(
                            v___x_2045_,
                            v_i_2055_,
                            v_a_2046_,
                            v_val_2061_,
                            v___x_2047_,
                            v___y_2052_,
                            v___y_2053_,
                        );
                    crate::leanh::lean_dec(v_val_2061_);
                    crate::leanh::lean_dec_ref(v_i_2055_);
                    if crate::leanh::lean_obj_tag(v___x_2062_) == 0 {
                        v_isSharedCheck_2070_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                        if v_isSharedCheck_2070_ == 0 {
                            v_unused_2071_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                            crate::leanh::lean_dec(v_unused_2071_);
                            v___x_2064_ = v___x_2062_;
                            v_isShared_2065_ = v_isSharedCheck_2070_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2062_);
                            v___x_2064_ = crate::leanh::lean_box(0);
                            v_isShared_2065_ = v_isSharedCheck_2070_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2072_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                        v_isSharedCheck_2079_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                        if v_isSharedCheck_2079_ == 0 {
                            v___x_2074_ = v___x_2062_;
                            v_isShared_2075_ = v_isSharedCheck_2079_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2072_);
                            crate::leanh::lean_dec(v___x_2062_);
                            v___x_2074_ = crate::leanh::lean_box(0);
                            v_isShared_2075_ = v_isSharedCheck_2079_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2060_);
                    crate::leanh::lean_dec_ref(v_i_2055_);
                    v___x_2080_ = crate::leanh::lean_box((v___x_2048_) as usize);
                    if v_isShared_2058_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2057_, 0);
                        crate::leanh::lean_ctor_set(v___x_2057_, 0, v___x_2080_);
                        v___x_2082_ = v___x_2057_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                        v___x_2082_ = v_reuseFailAlloc_2083_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2066_ = crate::leanh::lean_box((v___x_2048_) as usize);
                if v_isShared_2065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2066_);
                    v___x_2068_ = v___x_2064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
                    v___x_2068_ = v_reuseFailAlloc_2069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2068_;
            }
            4 => {
                if v_isShared_2075_ == 0 {
                    v___x_2077_ = v___x_2074_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2077_;
            }
            6 => {
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed(
    mut v___x_2087_: *mut crate::leanh::LeanObject,
    mut v___x_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v___x_2090_: *mut crate::leanh::LeanObject,
    mut v___x_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_info_2093_: *mut crate::leanh::LeanObject,
    mut v_x_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11275__boxed_2098_: u8 = 0;
    let mut v___x_11278__boxed_2099_: u8 = 0;
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11275__boxed_2098_ = (crate::leanh::lean_unbox(v___x_2088_) as u8);
    v___x_11278__boxed_2099_ = (crate::leanh::lean_unbox(v___x_2091_) as u8);
    v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1(v___x_2087_, v___x_11275__boxed_2098_, v_a_2089_, v___x_2090_, v___x_11278__boxed_2099_, v_x_2092_, v_info_2093_, v_x_2094_, v___y_2095_, v___y_2096_);
    crate::leanh::lean_dec(v___y_2096_);
    crate::leanh::lean_dec_ref(v___y_2095_);
    crate::leanh::lean_dec_ref(v_x_2094_);
    crate::leanh::lean_dec_ref(v_x_2092_);
    crate::leanh::lean_dec(v_a_2089_);
    crate::leanh::lean_dec(v___x_2087_);
    return v_res_2100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0(
    mut v___x_2101_: *mut crate::leanh::LeanObject,
    mut v_x_2102_: *mut crate::leanh::LeanObject,
    mut v_x_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
    mut v_x_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2101_);
    return v___x_2108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0___boxed(
    mut v___x_2109_: *mut crate::leanh::LeanObject,
    mut v_x_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
    mut v_x_2112_: *mut crate::leanh::LeanObject,
    mut v_x_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0(v___x_2109_, v_x_2110_, v_x_2111_, v_x_2112_, v_x_2113_, v___y_2114_);
    crate::leanh::lean_dec(v___y_2114_);
    crate::leanh::lean_dec_ref(v_x_2113_);
    crate::leanh::lean_dec_ref(v_x_2112_);
    crate::leanh::lean_dec_ref(v_x_2111_);
    crate::leanh::lean_dec_ref(v_x_2110_);
    return v_res_2116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(
    mut v___x_2122_: u8,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_as_2124_: *mut crate::leanh::LeanObject,
    mut v_sz_2125_: usize,
    mut v_i_2126_: usize,
    mut v_b_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: usize = 0;
    let mut v___x_2144_: usize = 0;
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2131_ = lean_usize_dec_lt(v_i_2126_, v_sz_2125_);
                if v___x_2131_ == 0 {
                    crate::leanh::lean_dec(v_a_2123_);
                    v___x_2132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2132_, 0, v_b_2127_);
                    return v___x_2132_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2127_);
                    v___x_2133_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
                    v___x_2134_ = crate::leanh::lean_box(0);
                    v___f_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0;
                    v___x_2136_ = crate::leanh::lean_box((v___x_2122_) as usize);
                    v___x_2137_ = crate::leanh::lean_box((v___x_2131_) as usize);
                    crate::leanh::lean_inc(v_a_2123_);
                    v___f_2138_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___f_2138_, 0, v___x_2133_);
                    crate::leanh::lean_closure_set(v___f_2138_, 1, v___x_2136_);
                    crate::leanh::lean_closure_set(v___f_2138_, 2, v_a_2123_);
                    crate::leanh::lean_closure_set(v___f_2138_, 3, v___x_2134_);
                    crate::leanh::lean_closure_set(v___f_2138_, 4, v___x_2137_);
                    v_a_2139_ = lean_array_uget_borrowed(v_as_2124_, v_i_2126_);
                    v___x_2140_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2139_);
                    v___x_2141_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
                            v___f_2138_,
                            v___f_2135_,
                            v___x_2140_,
                            v_a_2139_,
                            v___y_2128_,
                            v___y_2129_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2141_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2141_, 1);
                        v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1;
                        v___x_2143_ = 1usize;
                        v___x_2144_ = lean_usize_add(v_i_2126_, v___x_2143_);
                        v_i_2126_ = v___x_2144_;
                        v_b_2127_ = v___x_2142_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2123_);
                        v_a_2146_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                        v_isSharedCheck_2153_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2141_)) as u8;
                        if v_isSharedCheck_2153_ == 0 {
                            v___x_2148_ = v___x_2141_;
                            v_isShared_2149_ = v_isSharedCheck_2153_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2146_);
                            crate::leanh::lean_dec(v___x_2141_);
                            v___x_2148_ = crate::leanh::lean_box(0);
                            v_isShared_2149_ = v_isSharedCheck_2153_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2149_ == 0 {
                    v___x_2151_ = v___x_2148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
                    v___x_2151_ = v_reuseFailAlloc_2152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___boxed(
    mut v___x_2154_: *mut crate::leanh::LeanObject,
    mut v_a_2155_: *mut crate::leanh::LeanObject,
    mut v_as_2156_: *mut crate::leanh::LeanObject,
    mut v_sz_2157_: *mut crate::leanh::LeanObject,
    mut v_i_2158_: *mut crate::leanh::LeanObject,
    mut v_b_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11400__boxed_2163_: u8 = 0;
    let mut v_sz_boxed_2164_: usize = 0;
    let mut v_i_boxed_2165_: usize = 0;
    let mut v_res_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11400__boxed_2163_ = (crate::leanh::lean_unbox(v___x_2154_) as u8);
    v_sz_boxed_2164_ = crate::leanh::lean_unbox_usize(v_sz_2157_);
    crate::leanh::lean_dec(v_sz_2157_);
    v_i_boxed_2165_ = crate::leanh::lean_unbox_usize(v_i_2158_);
    crate::leanh::lean_dec(v_i_2158_);
    v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(v___x_11400__boxed_2163_, v_a_2155_, v_as_2156_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2159_, v___y_2160_, v___y_2161_);
    crate::leanh::lean_dec(v___y_2161_);
    crate::leanh::lean_dec_ref(v___y_2160_);
    crate::leanh::lean_dec_ref(v_as_2156_);
    return v_res_2166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(
    mut v___x_2167_: u8,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
    mut v_as_2169_: *mut crate::leanh::LeanObject,
    mut v_sz_2170_: usize,
    mut v_i_2171_: usize,
    mut v_b_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: usize = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2176_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
                if v___x_2176_ == 0 {
                    crate::leanh::lean_dec(v_a_2168_);
                    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2177_, 0, v_b_2172_);
                    return v___x_2177_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2172_);
                    v___x_2178_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
                    v___x_2179_ = crate::leanh::lean_box(0);
                    v___f_2180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0;
                    v___x_2181_ = crate::leanh::lean_box((v___x_2167_) as usize);
                    v___x_2182_ = crate::leanh::lean_box((v___x_2176_) as usize);
                    crate::leanh::lean_inc(v_a_2168_);
                    v___f_2183_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___f_2183_, 0, v___x_2178_);
                    crate::leanh::lean_closure_set(v___f_2183_, 1, v___x_2181_);
                    crate::leanh::lean_closure_set(v___f_2183_, 2, v_a_2168_);
                    crate::leanh::lean_closure_set(v___f_2183_, 3, v___x_2179_);
                    crate::leanh::lean_closure_set(v___f_2183_, 4, v___x_2182_);
                    v_a_2184_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
                    v___x_2185_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2184_);
                    v___x_2186_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
                            v___f_2183_,
                            v___f_2180_,
                            v___x_2185_,
                            v_a_2184_,
                            v___y_2173_,
                            v___y_2174_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2186_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2186_, 1);
                        v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1;
                        v___x_2188_ = 1usize;
                        v___x_2189_ = lean_usize_add(v_i_2171_, v___x_2188_);
                        v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(v___x_2167_, v_a_2168_, v_as_2169_, v_sz_2170_, v___x_2189_, v___x_2187_, v___y_2173_, v___y_2174_);
                        return v___x_2190_;
                    } else {
                        crate::leanh::lean_dec(v_a_2168_);
                        v_a_2191_ = crate::leanh::lean_ctor_get(v___x_2186_, 0);
                        v_isSharedCheck_2198_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2186_)) as u8;
                        if v_isSharedCheck_2198_ == 0 {
                            v___x_2193_ = v___x_2186_;
                            v_isShared_2194_ = v_isSharedCheck_2198_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2191_);
                            crate::leanh::lean_dec(v___x_2186_);
                            v___x_2193_ = crate::leanh::lean_box(0);
                            v_isShared_2194_ = v_isSharedCheck_2198_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2194_ == 0 {
                    v___x_2196_ = v___x_2193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15___boxed(
    mut v___x_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_as_2201_: *mut crate::leanh::LeanObject,
    mut v_sz_2202_: *mut crate::leanh::LeanObject,
    mut v_i_2203_: *mut crate::leanh::LeanObject,
    mut v_b_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11470__boxed_2208_: u8 = 0;
    let mut v_sz_boxed_2209_: usize = 0;
    let mut v_i_boxed_2210_: usize = 0;
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11470__boxed_2208_ = (crate::leanh::lean_unbox(v___x_2199_) as u8);
    v_sz_boxed_2209_ = crate::leanh::lean_unbox_usize(v_sz_2202_);
    crate::leanh::lean_dec(v_sz_2202_);
    v_i_boxed_2210_ = crate::leanh::lean_unbox_usize(v_i_2203_);
    crate::leanh::lean_dec(v_i_2203_);
    v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(v___x_11470__boxed_2208_, v_a_2200_, v_as_2201_, v_sz_boxed_2209_, v_i_boxed_2210_, v_b_2204_, v___y_2205_, v___y_2206_);
    crate::leanh::lean_dec(v___y_2206_);
    crate::leanh::lean_dec_ref(v___y_2205_);
    crate::leanh::lean_dec_ref(v_as_2201_);
    return v_res_2211_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(
    mut v_init_2212_: *mut crate::leanh::LeanObject,
    mut v___x_2213_: u8,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_n_2215_: *mut crate::leanh::LeanObject,
    mut v_b_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v_fst_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_vs_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2252_: usize = 0;
    let mut v___x_2253_: usize = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v_fst_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut v_a_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2273_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2215_) == 0 {
                    v_cs_2220_ = crate::leanh::lean_ctor_get(v_n_2215_, 0);
                    v___x_2221_ = crate::leanh::lean_box(0);
                    v___x_2222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                    crate::leanh::lean_ctor_set(v___x_2222_, 1, v_b_2216_);
                    v_sz_2223_ = lean_array_size(v_cs_2220_);
                    v___x_2224_ = 0usize;
                    v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(v_init_2212_, v___x_2213_, v_a_2214_, v_cs_2220_, v_sz_2223_, v___x_2224_, v___x_2222_, v___y_2217_, v___y_2218_);
                    if crate::leanh::lean_obj_tag(v___x_2225_) == 0 {
                        v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                        v_isSharedCheck_2240_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                        if v_isSharedCheck_2240_ == 0 {
                            v___x_2228_ = v___x_2225_;
                            v_isShared_2229_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2226_);
                            crate::leanh::lean_dec(v___x_2225_);
                            v___x_2228_ = crate::leanh::lean_box(0);
                            v_isShared_2229_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                        v_isSharedCheck_2248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                        if v_isSharedCheck_2248_ == 0 {
                            v___x_2243_ = v___x_2225_;
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2241_);
                            crate::leanh::lean_dec(v___x_2225_);
                            v___x_2243_ = crate::leanh::lean_box(0);
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2249_ = crate::leanh::lean_ctor_get(v_n_2215_, 0);
                    v___x_2250_ = crate::leanh::lean_box(0);
                    v___x_2251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 1, v_b_2216_);
                    v_sz_2252_ = lean_array_size(v_vs_2249_);
                    v___x_2253_ = 0usize;
                    v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(v___x_2213_, v_a_2214_, v_vs_2249_, v_sz_2252_, v___x_2253_, v___x_2251_, v___y_2217_, v___y_2218_);
                    if crate::leanh::lean_obj_tag(v___x_2254_) == 0 {
                        v_a_2255_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                        v_isSharedCheck_2269_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                        if v_isSharedCheck_2269_ == 0 {
                            v___x_2257_ = v___x_2254_;
                            v_isShared_2258_ = v_isSharedCheck_2269_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2255_);
                            crate::leanh::lean_dec(v___x_2254_);
                            v___x_2257_ = crate::leanh::lean_box(0);
                            v_isShared_2258_ = v_isSharedCheck_2269_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2270_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                        v_isSharedCheck_2277_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                        if v_isSharedCheck_2277_ == 0 {
                            v___x_2272_ = v___x_2254_;
                            v_isShared_2273_ = v_isSharedCheck_2277_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2270_);
                            crate::leanh::lean_dec(v___x_2254_);
                            v___x_2272_ = crate::leanh::lean_box(0);
                            v_isShared_2273_ = v_isSharedCheck_2277_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2230_ = crate::leanh::lean_ctor_get(v_a_2226_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2230_) == 0 {
                    v_snd_2231_ = crate::leanh::lean_ctor_get(v_a_2226_, 1);
                    crate::leanh::lean_inc(v_snd_2231_);
                    crate::leanh::lean_dec(v_a_2226_);
                    v___x_2232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2232_, 0, v_snd_2231_);
                    if v_isShared_2229_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2232_);
                        v___x_2234_ = v___x_2228_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
                        v___x_2234_ = v_reuseFailAlloc_2235_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2230_);
                    crate::leanh::lean_dec(v_a_2226_);
                    v_val_2236_ = crate::leanh::lean_ctor_get(v_fst_2230_, 0);
                    crate::leanh::lean_inc(v_val_2236_);
                    crate::leanh::lean_dec_ref_known(v_fst_2230_, 1);
                    if v_isShared_2229_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2228_, 0, v_val_2236_);
                        v___x_2238_ = v___x_2228_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_val_2236_);
                        v___x_2238_ = v_reuseFailAlloc_2239_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2234_;
            }
            3 => {
                return v___x_2238_;
            }
            4 => {
                if v_isShared_2244_ == 0 {
                    v___x_2246_ = v___x_2243_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
                    v___x_2246_ = v_reuseFailAlloc_2247_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2246_;
            }
            6 => {
                v_fst_2259_ = crate::leanh::lean_ctor_get(v_a_2255_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2259_) == 0 {
                    v_snd_2260_ = crate::leanh::lean_ctor_get(v_a_2255_, 1);
                    crate::leanh::lean_inc(v_snd_2260_);
                    crate::leanh::lean_dec(v_a_2255_);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v_snd_2260_);
                    if v_isShared_2258_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2261_);
                        v___x_2263_ = v___x_2257_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
                        v___x_2263_ = v_reuseFailAlloc_2264_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2259_);
                    crate::leanh::lean_dec(v_a_2255_);
                    v_val_2265_ = crate::leanh::lean_ctor_get(v_fst_2259_, 0);
                    crate::leanh::lean_inc(v_val_2265_);
                    crate::leanh::lean_dec_ref_known(v_fst_2259_, 1);
                    if v_isShared_2258_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2257_, 0, v_val_2265_);
                        v___x_2267_ = v___x_2257_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_val_2265_);
                        v___x_2267_ = v_reuseFailAlloc_2268_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2263_;
            }
            8 => {
                return v___x_2267_;
            }
            9 => {
                if v_isShared_2273_ == 0 {
                    v___x_2275_ = v___x_2272_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
                    v___x_2275_ = v_reuseFailAlloc_2276_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(
    mut v_init_2278_: *mut crate::leanh::LeanObject,
    mut v___x_2279_: u8,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_as_2281_: *mut crate::leanh::LeanObject,
    mut v_sz_2282_: usize,
    mut v_i_2283_: usize,
    mut v_b_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v_a_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: usize = 0;
    let mut v___x_2312_: usize = 0;
    let mut v_reuseFailAlloc_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_a_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2319_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_unused_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = lean_usize_dec_lt(v_i_2283_, v_sz_2282_);
                if v___x_2288_ == 0 {
                    crate::leanh::lean_dec(v_a_2280_);
                    v___x_2289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v_b_2284_);
                    return v___x_2289_;
                } else {
                    v_snd_2290_ = crate::leanh::lean_ctor_get(v_b_2284_, 1);
                    v_isSharedCheck_2324_ = (!crate::leanh::lean_is_exclusive(v_b_2284_)) as u8;
                    if v_isSharedCheck_2324_ == 0 {
                        v_unused_2325_ = crate::leanh::lean_ctor_get(v_b_2284_, 0);
                        crate::leanh::lean_dec(v_unused_2325_);
                        v___x_2292_ = v_b_2284_;
                        v_isShared_2293_ = v_isSharedCheck_2324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2290_);
                        crate::leanh::lean_dec(v_b_2284_);
                        v___x_2292_ = crate::leanh::lean_box(0);
                        v_isShared_2293_ = v_isSharedCheck_2324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2294_ = lean_array_uget_borrowed(v_as_2281_, v_i_2283_);
                crate::leanh::lean_inc(v_snd_2290_);
                crate::leanh::lean_inc(v_a_2280_);
                v___x_2295_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_init_2278_, v___x_2279_, v_a_2280_, v_a_2294_, v_snd_2290_, v___y_2285_, v___y_2286_);
                if crate::leanh::lean_obj_tag(v___x_2295_) == 0 {
                    v_a_2296_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                    v_isSharedCheck_2315_ = (!crate::leanh::lean_is_exclusive(v___x_2295_)) as u8;
                    if v_isSharedCheck_2315_ == 0 {
                        v___x_2298_ = v___x_2295_;
                        v_isShared_2299_ = v_isSharedCheck_2315_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2296_);
                        crate::leanh::lean_dec(v___x_2295_);
                        v___x_2298_ = crate::leanh::lean_box(0);
                        v_isShared_2299_ = v_isSharedCheck_2315_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2292_);
                    crate::leanh::lean_dec(v_snd_2290_);
                    crate::leanh::lean_dec(v_a_2280_);
                    v_a_2316_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                    v_isSharedCheck_2323_ = (!crate::leanh::lean_is_exclusive(v___x_2295_)) as u8;
                    if v_isSharedCheck_2323_ == 0 {
                        v___x_2318_ = v___x_2295_;
                        v_isShared_2319_ = v_isSharedCheck_2323_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2316_);
                        crate::leanh::lean_dec(v___x_2295_);
                        v___x_2318_ = crate::leanh::lean_box(0);
                        v_isShared_2319_ = v_isSharedCheck_2323_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2296_) == 0 {
                    crate::leanh::lean_dec(v_a_2280_);
                    v___x_2300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2300_, 0, v_a_2296_);
                    if v_isShared_2293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2300_);
                        v___x_2302_ = v___x_2292_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_snd_2290_);
                        v___x_2302_ = v_reuseFailAlloc_2306_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2298_);
                    crate::leanh::lean_dec(v_snd_2290_);
                    v_a_2307_ = crate::leanh::lean_ctor_get(v_a_2296_, 0);
                    crate::leanh::lean_inc(v_a_2307_);
                    crate::leanh::lean_dec_ref_known(v_a_2296_, 1);
                    v___x_2308_ = crate::leanh::lean_box(0);
                    if v_isShared_2293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2292_, 1, v_a_2307_);
                        crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2308_);
                        v___x_2310_ = v___x_2292_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2308_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_a_2307_);
                        v___x_2310_ = v_reuseFailAlloc_2314_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2298_, 0, v___x_2302_);
                    v___x_2304_ = v___x_2298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
                    v___x_2304_ = v_reuseFailAlloc_2305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2304_;
            }
            5 => {
                v___x_2311_ = 1usize;
                v___x_2312_ = lean_usize_add(v_i_2283_, v___x_2311_);
                v_i_2283_ = v___x_2312_;
                v_b_2284_ = v___x_2310_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2319_ == 0 {
                    v___x_2321_ = v___x_2318_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
                    v___x_2321_ = v_reuseFailAlloc_2322_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14___boxed(
    mut v_init_2326_: *mut crate::leanh::LeanObject,
    mut v___x_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_as_2329_: *mut crate::leanh::LeanObject,
    mut v_sz_2330_: *mut crate::leanh::LeanObject,
    mut v_i_2331_: *mut crate::leanh::LeanObject,
    mut v_b_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11530__boxed_2336_: u8 = 0;
    let mut v_sz_boxed_2337_: usize = 0;
    let mut v_i_boxed_2338_: usize = 0;
    let mut v_res_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11530__boxed_2336_ = (crate::leanh::lean_unbox(v___x_2327_) as u8);
    v_sz_boxed_2337_ = crate::leanh::lean_unbox_usize(v_sz_2330_);
    crate::leanh::lean_dec(v_sz_2330_);
    v_i_boxed_2338_ = crate::leanh::lean_unbox_usize(v_i_2331_);
    crate::leanh::lean_dec(v_i_2331_);
    v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(v_init_2326_, v___x_11530__boxed_2336_, v_a_2328_, v_as_2329_, v_sz_boxed_2337_, v_i_boxed_2338_, v_b_2332_, v___y_2333_, v___y_2334_);
    crate::leanh::lean_dec(v___y_2334_);
    crate::leanh::lean_dec_ref(v___y_2333_);
    crate::leanh::lean_dec_ref(v_as_2329_);
    return v_res_2339_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(
    mut v_init_2340_: *mut crate::leanh::LeanObject,
    mut v___x_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_n_2343_: *mut crate::leanh::LeanObject,
    mut v_b_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11551__boxed_2348_: u8 = 0;
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11551__boxed_2348_ = (crate::leanh::lean_unbox(v___x_2341_) as u8);
    v_res_2349_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_init_2340_, v___x_11551__boxed_2348_, v_a_2342_, v_n_2343_, v_b_2344_, v___y_2345_, v___y_2346_);
    crate::leanh::lean_dec(v___y_2346_);
    crate::leanh::lean_dec_ref(v___y_2345_);
    crate::leanh::lean_dec_ref(v_n_2343_);
    return v_res_2349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(
    mut v___x_2353_: u8,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_as_2355_: *mut crate::leanh::LeanObject,
    mut v_sz_2356_: usize,
    mut v_i_2357_: usize,
    mut v_b_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: usize = 0;
    let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2362_ = lean_usize_dec_lt(v_i_2357_, v_sz_2356_);
                if v___x_2362_ == 0 {
                    crate::leanh::lean_dec(v_a_2354_);
                    v___x_2363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2363_, 0, v_b_2358_);
                    return v___x_2363_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2358_);
                    v___x_2364_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
                    v___x_2365_ = crate::leanh::lean_box(0);
                    v___f_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0;
                    v___x_2367_ = crate::leanh::lean_box((v___x_2353_) as usize);
                    v___x_2368_ = crate::leanh::lean_box((v___x_2362_) as usize);
                    crate::leanh::lean_inc(v_a_2354_);
                    v___f_2369_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___f_2369_, 0, v___x_2364_);
                    crate::leanh::lean_closure_set(v___f_2369_, 1, v___x_2367_);
                    crate::leanh::lean_closure_set(v___f_2369_, 2, v_a_2354_);
                    crate::leanh::lean_closure_set(v___f_2369_, 3, v___x_2365_);
                    crate::leanh::lean_closure_set(v___f_2369_, 4, v___x_2368_);
                    v_a_2370_ = lean_array_uget_borrowed(v_as_2355_, v_i_2357_);
                    v___x_2371_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2370_);
                    v___x_2372_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
                            v___f_2369_,
                            v___f_2366_,
                            v___x_2371_,
                            v_a_2370_,
                            v___y_2359_,
                            v___y_2360_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2372_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2372_, 1);
                        v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0;
                        v___x_2374_ = 1usize;
                        v___x_2375_ = lean_usize_add(v_i_2357_, v___x_2374_);
                        v_i_2357_ = v___x_2375_;
                        v_b_2358_ = v___x_2373_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2354_);
                        v_a_2377_ = crate::leanh::lean_ctor_get(v___x_2372_, 0);
                        v_isSharedCheck_2384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2372_)) as u8;
                        if v_isSharedCheck_2384_ == 0 {
                            v___x_2379_ = v___x_2372_;
                            v_isShared_2380_ = v_isSharedCheck_2384_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2377_);
                            crate::leanh::lean_dec(v___x_2372_);
                            v___x_2379_ = crate::leanh::lean_box(0);
                            v_isShared_2380_ = v_isSharedCheck_2384_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2380_ == 0 {
                    v___x_2382_ = v___x_2379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
                    v___x_2382_ = v_reuseFailAlloc_2383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___boxed(
    mut v___x_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_as_2387_: *mut crate::leanh::LeanObject,
    mut v_sz_2388_: *mut crate::leanh::LeanObject,
    mut v_i_2389_: *mut crate::leanh::LeanObject,
    mut v_b_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11745__boxed_2394_: u8 = 0;
    let mut v_sz_boxed_2395_: usize = 0;
    let mut v_i_boxed_2396_: usize = 0;
    let mut v_res_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11745__boxed_2394_ = (crate::leanh::lean_unbox(v___x_2385_) as u8);
    v_sz_boxed_2395_ = crate::leanh::lean_unbox_usize(v_sz_2388_);
    crate::leanh::lean_dec(v_sz_2388_);
    v_i_boxed_2396_ = crate::leanh::lean_unbox_usize(v_i_2389_);
    crate::leanh::lean_dec(v_i_2389_);
    v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(v___x_11745__boxed_2394_, v_a_2386_, v_as_2387_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2390_, v___y_2391_, v___y_2392_);
    crate::leanh::lean_dec(v___y_2392_);
    crate::leanh::lean_dec_ref(v___y_2391_);
    crate::leanh::lean_dec_ref(v_as_2387_);
    return v_res_2397_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(
    mut v___x_2398_: u8,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_as_2400_: *mut crate::leanh::LeanObject,
    mut v_sz_2401_: usize,
    mut v_i_2402_: usize,
    mut v_b_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: usize = 0;
    let mut v___x_2420_: usize = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2407_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
                if v___x_2407_ == 0 {
                    crate::leanh::lean_dec(v_a_2399_);
                    v___x_2408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2408_, 0, v_b_2403_);
                    return v___x_2408_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2403_);
                    v___x_2409_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
                    v___x_2410_ = crate::leanh::lean_box(0);
                    v___f_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0;
                    v___x_2412_ = crate::leanh::lean_box((v___x_2398_) as usize);
                    v___x_2413_ = crate::leanh::lean_box((v___x_2407_) as usize);
                    crate::leanh::lean_inc(v_a_2399_);
                    v___f_2414_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___f_2414_, 0, v___x_2409_);
                    crate::leanh::lean_closure_set(v___f_2414_, 1, v___x_2412_);
                    crate::leanh::lean_closure_set(v___f_2414_, 2, v_a_2399_);
                    crate::leanh::lean_closure_set(v___f_2414_, 3, v___x_2410_);
                    crate::leanh::lean_closure_set(v___f_2414_, 4, v___x_2413_);
                    v_a_2415_ = lean_array_uget_borrowed(v_as_2400_, v_i_2402_);
                    v___x_2416_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2415_);
                    v___x_2417_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(
                            v___f_2414_,
                            v___f_2411_,
                            v___x_2416_,
                            v_a_2415_,
                            v___y_2404_,
                            v___y_2405_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2417_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2417_, 1);
                        v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0;
                        v___x_2419_ = 1usize;
                        v___x_2420_ = lean_usize_add(v_i_2402_, v___x_2419_);
                        v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(v___x_2398_, v_a_2399_, v_as_2400_, v_sz_2401_, v___x_2420_, v___x_2418_, v___y_2404_, v___y_2405_);
                        return v___x_2421_;
                    } else {
                        crate::leanh::lean_dec(v_a_2399_);
                        v_a_2422_ = crate::leanh::lean_ctor_get(v___x_2417_, 0);
                        v_isSharedCheck_2429_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2417_)) as u8;
                        if v_isSharedCheck_2429_ == 0 {
                            v___x_2424_ = v___x_2417_;
                            v_isShared_2425_ = v_isSharedCheck_2429_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2422_);
                            crate::leanh::lean_dec(v___x_2417_);
                            v___x_2424_ = crate::leanh::lean_box(0);
                            v_isShared_2425_ = v_isSharedCheck_2429_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2425_ == 0 {
                    v___x_2427_ = v___x_2424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___boxed(
    mut v___x_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
    mut v_as_2432_: *mut crate::leanh::LeanObject,
    mut v_sz_2433_: *mut crate::leanh::LeanObject,
    mut v_i_2434_: *mut crate::leanh::LeanObject,
    mut v_b_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11813__boxed_2439_: u8 = 0;
    let mut v_sz_boxed_2440_: usize = 0;
    let mut v_i_boxed_2441_: usize = 0;
    let mut v_res_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11813__boxed_2439_ = (crate::leanh::lean_unbox(v___x_2430_) as u8);
    v_sz_boxed_2440_ = crate::leanh::lean_unbox_usize(v_sz_2433_);
    crate::leanh::lean_dec(v_sz_2433_);
    v_i_boxed_2441_ = crate::leanh::lean_unbox_usize(v_i_2434_);
    crate::leanh::lean_dec(v_i_2434_);
    v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(v___x_11813__boxed_2439_, v_a_2431_, v_as_2432_, v_sz_boxed_2440_, v_i_boxed_2441_, v_b_2435_, v___y_2436_, v___y_2437_);
    crate::leanh::lean_dec(v___y_2437_);
    crate::leanh::lean_dec_ref(v___y_2436_);
    crate::leanh::lean_dec_ref(v_as_2432_);
    return v_res_2442_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(
    mut v___x_2443_: u8,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_t_2445_: *mut crate::leanh::LeanObject,
    mut v_init_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v_a_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2464_: usize = 0;
    let mut v___x_2465_: usize = 0;
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v_fst_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2480_: u8 = 0;
    let mut v_a_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v_a_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2450_ = crate::leanh::lean_ctor_get(v_t_2445_, 0);
                v_tail_2451_ = crate::leanh::lean_ctor_get(v_t_2445_, 1);
                crate::leanh::lean_inc(v_a_2444_);
                v___x_2452_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_init_2446_, v___x_2443_, v_a_2444_, v_root_2450_, v_init_2446_, v___y_2447_, v___y_2448_);
                if crate::leanh::lean_obj_tag(v___x_2452_) == 0 {
                    v_a_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                    v_isSharedCheck_2489_ = (!crate::leanh::lean_is_exclusive(v___x_2452_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2455_ = v___x_2452_;
                        v_isShared_2456_ = v_isSharedCheck_2489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2453_);
                        crate::leanh::lean_dec(v___x_2452_);
                        v___x_2455_ = crate::leanh::lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2489_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2444_);
                    v_a_2490_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                    v_isSharedCheck_2497_ = (!crate::leanh::lean_is_exclusive(v___x_2452_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v___x_2492_ = v___x_2452_;
                        v_isShared_2493_ = v_isSharedCheck_2497_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2490_);
                        crate::leanh::lean_dec(v___x_2452_);
                        v___x_2492_ = crate::leanh::lean_box(0);
                        v_isShared_2493_ = v_isSharedCheck_2497_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2453_) == 0 {
                    crate::leanh::lean_dec(v_a_2444_);
                    v_a_2457_ = crate::leanh::lean_ctor_get(v_a_2453_, 0);
                    crate::leanh::lean_inc(v_a_2457_);
                    crate::leanh::lean_dec_ref_known(v_a_2453_, 1);
                    if v_isShared_2456_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2455_, 0, v_a_2457_);
                        v___x_2459_ = v___x_2455_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2457_);
                        v___x_2459_ = v_reuseFailAlloc_2460_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2455_);
                    v_a_2461_ = crate::leanh::lean_ctor_get(v_a_2453_, 0);
                    crate::leanh::lean_inc(v_a_2461_);
                    crate::leanh::lean_dec_ref_known(v_a_2453_, 1);
                    v___x_2462_ = crate::leanh::lean_box(0);
                    v___x_2463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    crate::leanh::lean_ctor_set(v___x_2463_, 1, v_a_2461_);
                    v_sz_2464_ = lean_array_size(v_tail_2451_);
                    v___x_2465_ = 0usize;
                    v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(v___x_2443_, v_a_2444_, v_tail_2451_, v_sz_2464_, v___x_2465_, v___x_2463_, v___y_2447_, v___y_2448_);
                    if crate::leanh::lean_obj_tag(v___x_2466_) == 0 {
                        v_a_2467_ = crate::leanh::lean_ctor_get(v___x_2466_, 0);
                        v_isSharedCheck_2480_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2466_)) as u8;
                        if v_isSharedCheck_2480_ == 0 {
                            v___x_2469_ = v___x_2466_;
                            v_isShared_2470_ = v_isSharedCheck_2480_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2467_);
                            crate::leanh::lean_dec(v___x_2466_);
                            v___x_2469_ = crate::leanh::lean_box(0);
                            v_isShared_2470_ = v_isSharedCheck_2480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2481_ = crate::leanh::lean_ctor_get(v___x_2466_, 0);
                        v_isSharedCheck_2488_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2466_)) as u8;
                        if v_isSharedCheck_2488_ == 0 {
                            v___x_2483_ = v___x_2466_;
                            v_isShared_2484_ = v_isSharedCheck_2488_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2481_);
                            crate::leanh::lean_dec(v___x_2466_);
                            v___x_2483_ = crate::leanh::lean_box(0);
                            v_isShared_2484_ = v_isSharedCheck_2488_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2459_;
            }
            3 => {
                v_fst_2471_ = crate::leanh::lean_ctor_get(v_a_2467_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2471_) == 0 {
                    v_snd_2472_ = crate::leanh::lean_ctor_get(v_a_2467_, 1);
                    crate::leanh::lean_inc(v_snd_2472_);
                    crate::leanh::lean_dec(v_a_2467_);
                    if v_isShared_2470_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2469_, 0, v_snd_2472_);
                        v___x_2474_ = v___x_2469_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_snd_2472_);
                        v___x_2474_ = v_reuseFailAlloc_2475_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2471_);
                    crate::leanh::lean_dec(v_a_2467_);
                    v_val_2476_ = crate::leanh::lean_ctor_get(v_fst_2471_, 0);
                    crate::leanh::lean_inc(v_val_2476_);
                    crate::leanh::lean_dec_ref_known(v_fst_2471_, 1);
                    if v_isShared_2470_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2469_, 0, v_val_2476_);
                        v___x_2478_ = v___x_2469_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_val_2476_);
                        v___x_2478_ = v_reuseFailAlloc_2479_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2474_;
            }
            5 => {
                return v___x_2478_;
            }
            6 => {
                if v_isShared_2484_ == 0 {
                    v___x_2486_ = v___x_2483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
                    v___x_2486_ = v_reuseFailAlloc_2487_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2486_;
            }
            8 => {
                if v_isShared_2493_ == 0 {
                    v___x_2495_ = v___x_2492_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
                    v___x_2495_ = v_reuseFailAlloc_2496_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(
    mut v___x_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_t_2500_: *mut crate::leanh::LeanObject,
    mut v_init_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11873__boxed_2505_: u8 = 0;
    let mut v_res_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11873__boxed_2505_ = (crate::leanh::lean_unbox(v___x_2498_) as u8);
    v_res_2506_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(
        v___x_11873__boxed_2505_,
        v_a_2499_,
        v_t_2500_,
        v_init_2501_,
        v___y_2502_,
        v___y_2503_,
    );
    crate::leanh::lean_dec(v___y_2503_);
    crate::leanh::lean_dec_ref(v___y_2502_);
    crate::leanh::lean_dec_ref(v_t_2500_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(
    mut v_o_2507_: *mut crate::leanh::LeanObject,
    mut v___y_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = lean_st_ref_get(v___y_2508_);
    v_env_2511_ = crate::leanh::lean_ctor_get(v___x_2510_, 0);
    crate::leanh::lean_inc_ref(v_env_2511_);
    crate::leanh::lean_dec(v___x_2510_);
    v___x_2512_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
    v_asyncMode_2514_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2513_, 2);
    v___x_2515_ = crate::leanh::lean_box(1);
    v___x_2516_ = crate::leanh::lean_box(0);
    v_linterSets_2517_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2515_,
        v___x_2512_,
        v_env_2511_,
        v_asyncMode_2514_,
        v___x_2516_,
    );
    v___x_2518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2518_, 0, v_o_2507_);
    crate::leanh::lean_ctor_set(v___x_2518_, 1, v_linterSets_2517_);
    v___x_2519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    return v___x_2519_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(
    mut v_o_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2523_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_2520_, v___y_2521_);
    crate::leanh::lean_dec(v___y_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = lean_st_ref_get(v___y_2525_);
    v_scopes_2528_ = crate::leanh::lean_ctor_get(v___x_2527_, 2);
    crate::leanh::lean_inc(v_scopes_2528_);
    crate::leanh::lean_dec(v___x_2527_);
    v___x_2529_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2530_ = l_List_head_x21___redArg(v___x_2529_, v_scopes_2528_);
    crate::leanh::lean_dec(v_scopes_2528_);
    v_opts_2531_ = crate::leanh::lean_ctor_get(v___x_2530_, 1);
    crate::leanh::lean_inc_ref(v_opts_2531_);
    crate::leanh::lean_dec(v___x_2530_);
    v___x_2532_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_opts_2531_, v___y_2525_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2536_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(
        v___y_2533_,
        v___y_2534_,
    );
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec_ref(v___y_2533_);
    return v_res_2536_;
}
pub unsafe fn l_Lean_Linter_Coe_coeLinter___lam__0(
    mut v_x_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_unused_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2541_ =
                    l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(
                        v___y_2539_,
                    );
                v_a_2542_ = crate::leanh::lean_ctor_get(v___x_2541_, 0);
                crate::leanh::lean_inc(v_a_2542_);
                crate::leanh::lean_dec_ref(v___x_2541_);
                v___x_2543_ =
                    l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(
                        v___y_2538_,
                        v___y_2539_,
                    );
                v_a_2544_ = crate::leanh::lean_ctor_get(v___x_2543_, 0);
                crate::leanh::lean_inc(v_a_2544_);
                crate::leanh::lean_dec_ref(v___x_2543_);
                v___x_2545_ =
                    l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(
                        v___y_2539_,
                    );
                v_a_2546_ = crate::leanh::lean_ctor_get(v___x_2545_, 0);
                crate::leanh::lean_inc(v_a_2546_);
                crate::leanh::lean_dec_ref(v___x_2545_);
                v___x_2547_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
                v___x_2548_ = l_Lean_Linter_getLinterValue(v___x_2547_, v_a_2544_);
                crate::leanh::lean_dec(v_a_2544_);
                v___x_2549_ = crate::leanh::lean_box(0);
                v___x_2550_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(
                        v___x_2548_,
                        v_a_2542_,
                        v_a_2546_,
                        v___x_2549_,
                        v___y_2538_,
                        v___y_2539_,
                    );
                crate::leanh::lean_dec(v_a_2546_);
                if crate::leanh::lean_obj_tag(v___x_2550_) == 0 {
                    v_isSharedCheck_2557_ = (!crate::leanh::lean_is_exclusive(v___x_2550_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v_unused_2558_ = crate::leanh::lean_ctor_get(v___x_2550_, 0);
                        crate::leanh::lean_dec(v_unused_2558_);
                        v___x_2552_ = v___x_2550_;
                        v_isShared_2553_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2550_);
                        v___x_2552_ = crate::leanh::lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2550_;
                }
            }
            1 => {
                if v_isShared_2553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2549_);
                    v___x_2555_ = v___x_2552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2549_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Coe_coeLinter___lam__0___boxed(
    mut v_x_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2563_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_2559_, v___y_2560_, v___y_2561_);
    crate::leanh::lean_dec(v___y_2561_);
    crate::leanh::lean_dec_ref(v___y_2560_);
    crate::leanh::lean_dec(v_x_2559_);
    return v_res_2563_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(
    mut v_o_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_2575_, v___y_2577_);
    return v___x_2579_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(
    mut v_o_2580_: *mut crate::leanh::LeanObject,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_2580_, v___y_2581_, v___y_2582_);
    crate::leanh::lean_dec(v___y_2582_);
    crate::leanh::lean_dec_ref(v___y_2581_);
    return v_res_2584_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5(
    mut v___x_2585_: u8,
    mut v_i_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_as_2588_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2589_: *mut crate::leanh::LeanObject,
    mut v_b_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2595_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(
        v___x_2585_,
        v_i_2586_,
        v_a_2587_,
        v_as_x27_2589_,
        v_b_2590_,
        v___y_2592_,
        v___y_2593_,
    );
    return v___x_2595_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(
    mut v___x_2596_: *mut crate::leanh::LeanObject,
    mut v_i_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_as_2599_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2600_: *mut crate::leanh::LeanObject,
    mut v_b_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12108__boxed_2606_: u8 = 0;
    let mut v_res_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12108__boxed_2606_ = (crate::leanh::lean_unbox(v___x_2596_) as u8);
    v_res_2607_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5(
        v___x_12108__boxed_2606_,
        v_i_2597_,
        v_a_2598_,
        v_as_2599_,
        v_as_x27_2600_,
        v_b_2601_,
        v_a_2602_,
        v___y_2603_,
        v___y_2604_,
    );
    crate::leanh::lean_dec(v___y_2604_);
    crate::leanh::lean_dec_ref(v___y_2603_);
    crate::leanh::lean_dec(v_as_x27_2600_);
    crate::leanh::lean_dec(v_as_2599_);
    crate::leanh::lean_dec(v_a_2598_);
    crate::leanh::lean_dec_ref(v_i_2597_);
    return v_res_2607_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6(
    mut v_msgData_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v_msgData_2608_, v___y_2610_);
    return v___x_2612_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___boxed(
    mut v_msgData_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6(v_msgData_2613_, v___y_2614_, v___y_2615_);
    crate::leanh::lean_dec(v___y_2615_);
    crate::leanh::lean_dec_ref(v___y_2614_);
    return v_res_2617_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10(
    mut v_00_u03b1_2618_: *mut crate::leanh::LeanObject,
    mut v_msg_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v_msg_2619_, v___y_2620_, v___y_2621_);
    return v___x_2623_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_2624_: *mut crate::leanh::LeanObject,
    mut v_msg_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10(v_00_u03b1_2624_, v_msg_2625_, v___y_2626_, v___y_2627_);
    crate::leanh::lean_dec(v___y_2627_);
    crate::leanh::lean_dec_ref(v___y_2626_);
    return v_res_2629_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8(
    mut v_00_u03b1_2630_: *mut crate::leanh::LeanObject,
    mut v_preNode_2631_: *mut crate::leanh::LeanObject,
    mut v_postNode_2632_: *mut crate::leanh::LeanObject,
    mut v_x_2633_: *mut crate::leanh::LeanObject,
    mut v_x_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_2631_, v_postNode_2632_, v_x_2633_, v_x_2634_, v___y_2635_, v___y_2636_);
    return v___x_2638_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___boxed(
    mut v_00_u03b1_2639_: *mut crate::leanh::LeanObject,
    mut v_preNode_2640_: *mut crate::leanh::LeanObject,
    mut v_postNode_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
    mut v_x_2643_: *mut crate::leanh::LeanObject,
    mut v___y_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8(v_00_u03b1_2639_, v_preNode_2640_, v_postNode_2641_, v_x_2642_, v_x_2643_, v___y_2644_, v___y_2645_);
    crate::leanh::lean_dec(v___y_2645_);
    crate::leanh::lean_dec_ref(v___y_2644_);
    return v_res_2647_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11(
    mut v_00_u03b1_2648_: *mut crate::leanh::LeanObject,
    mut v_preNode_2649_: *mut crate::leanh::LeanObject,
    mut v_postNode_2650_: *mut crate::leanh::LeanObject,
    mut v___x_2651_: *mut crate::leanh::LeanObject,
    mut v_x_2652_: *mut crate::leanh::LeanObject,
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_2649_, v_postNode_2650_, v___x_2651_, v_x_2652_, v_x_2653_, v___y_2654_, v___y_2655_);
    return v___x_2657_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___boxed(
    mut v_00_u03b1_2658_: *mut crate::leanh::LeanObject,
    mut v_preNode_2659_: *mut crate::leanh::LeanObject,
    mut v_postNode_2660_: *mut crate::leanh::LeanObject,
    mut v___x_2661_: *mut crate::leanh::LeanObject,
    mut v_x_2662_: *mut crate::leanh::LeanObject,
    mut v_x_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2667_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11(v_00_u03b1_2658_, v_preNode_2659_, v_postNode_2660_, v___x_2661_, v_x_2662_, v_x_2663_, v___y_2664_, v___y_2665_);
    crate::leanh::lean_dec(v___y_2665_);
    crate::leanh::lean_dec_ref(v___y_2664_);
    return v_res_2667_;
}
pub unsafe fn l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Lean_Linter_Coe_coeLinter;
    v___x_2670_ = l_Lean_Elab_Command_addLinter(v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(
    mut v_a_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
    return v_res_2672_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Coe_linter_deprecatedCoercions = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_Coe_linter_deprecatedCoercions);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Coe(builtin);
}
