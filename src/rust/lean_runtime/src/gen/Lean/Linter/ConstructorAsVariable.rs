// Lean compiler output
// Module: Lean.Linter.ConstructorAsVariable
// Imports: Lean.Elab.Command Lean.Linter.Util
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Syntax_getHeadInfo, l_Lean_Syntax_getId, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_toArray___redArg, l_Lean_PersistentArray_toList___redArg,
};
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
    l_Lean_Elab_TermInfo_runMetaM___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_getAppFn_x27, l_Lean_Expr_hasMVar};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_userName, lean_local_ctx_find};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_inferType___boxed;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Server::InfoUtils::{l_Lean_Elab_Info_range_x3f, l_Lean_Elab_Info_stx};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_contains, l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instBEqRange_beq,
    l_Lean_Syntax_instHashableRange_hash,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 78, 97, 109, 101, 65, 115, 86, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2048112346130701713 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 108, 105, 110, 116, 101, 114, 32, 116, 104, 97, 116, 32, 119, 97, 114, 110, 115, 32, 119, 104, 101, 110, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110, 97, 109, 101, 115, 32, 97, 114, 101, 32, 110, 117, 108, 108, 97, 114, 121, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3378770564748755370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_linter_constructorNameAsVariable: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [76, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 114, 101, 115, 101, 109, 98, 108, 101, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [39, 32, 45, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [119, 114, 105, 116, 101, 32, 39, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [39, 32, 40, 119, 105, 116, 104, 32, 97, 32, 100, 111, 116, 41, 32, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 116, 111, 32, 117, 115, 101, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_constructorNameAsVariable___closed__0_value:
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
    m_fun: l_Lean_Linter_constructorNameAsVariable___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_constructorNameAsVariable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_constructorNameAsVariable___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,18151959854494862315 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_constructorNameAsVariable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_constructorNameAsVariable___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_constructorNameAsVariable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_constructorNameAsVariable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(
    mut v_name_1592_: *mut crate::leanh::LeanObject,
    mut v_decl_1593_: *mut crate::leanh::LeanObject,
    mut v_ref_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut v_unused_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1596_ = crate::leanh::lean_ctor_get(v_decl_1593_, 0);
                v_descr_1597_ = crate::leanh::lean_ctor_get(v_decl_1593_, 1);
                v_deprecation_x3f_1598_ = crate::leanh::lean_ctor_get(v_decl_1593_, 2);
                v___x_1599_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1600_ = (crate::leanh::lean_unbox(v_defValue_1596_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_1599_, 0 as u32, v___x_1600_);
                crate::leanh::lean_inc(v_deprecation_x3f_1598_);
                crate::leanh::lean_inc_ref(v_descr_1597_);
                crate::leanh::lean_inc_n(v_name_1592_, 2);
                v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1601_, 0, v_name_1592_);
                crate::leanh::lean_ctor_set(v___x_1601_, 1, v_ref_1594_);
                crate::leanh::lean_ctor_set(v___x_1601_, 2, v___x_1599_);
                crate::leanh::lean_ctor_set(v___x_1601_, 3, v_descr_1597_);
                crate::leanh::lean_ctor_set(v___x_1601_, 4, v_deprecation_x3f_1598_);
                v___x_1602_ = lean_register_option(v_name_1592_, v___x_1601_);
                if crate::leanh::lean_obj_tag(v___x_1602_) == 0 {
                    v_isSharedCheck_1610_ = (!crate::leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1610_ == 0 {
                        v_unused_1611_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                        crate::leanh::lean_dec(v_unused_1611_);
                        v___x_1604_ = v___x_1602_;
                        v_isShared_1605_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1602_);
                        v___x_1604_ = crate::leanh::lean_box(0);
                        v_isShared_1605_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1592_);
                    v_a_1612_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1619_ = (!crate::leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1614_ = v___x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1612_);
                        crate::leanh::lean_dec(v___x_1602_);
                        v___x_1614_ = crate::leanh::lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_1596_);
                v___x_1606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1606_, 0, v_name_1592_);
                crate::leanh::lean_ctor_set(v___x_1606_, 1, v_defValue_1596_);
                if v_isShared_1605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1606_);
                    v___x_1608_ = v___x_1604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
                    v___x_1608_ = v_reuseFailAlloc_1609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1608_;
            }
            3 => {
                if v_isShared_1615_ == 0 {
                    v___x_1617_ = v___x_1614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
                    v___x_1617_ = v_reuseFailAlloc_1618_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1620_: *mut crate::leanh::LeanObject,
    mut v_decl_1621_: *mut crate::leanh::LeanObject,
    mut v_ref_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v_name_1620_, v_decl_1621_, v_ref_1622_);
    crate::leanh::lean_dec_ref(v_decl_1621_);
    return v_res_1624_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1645_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1646_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1647_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v___x_1644_, v___x_1645_, v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(
    mut v_a_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1649_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
    return v_res_1649_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(
    mut v_o_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = lean_st_ref_get(v___y_1651_);
    v_env_1654_ = crate::leanh::lean_ctor_get(v___x_1653_, 0);
    crate::leanh::lean_inc_ref(v_env_1654_);
    crate::leanh::lean_dec(v___x_1653_);
    v___x_1655_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_1656_ = crate::leanh::lean_ctor_get(v___x_1655_, 0);
    v_asyncMode_1657_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1656_, 2);
    v___x_1658_ = crate::leanh::lean_box(1);
    v___x_1659_ = crate::leanh::lean_box(0);
    v_linterSets_1660_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1658_,
        v___x_1655_,
        v_env_1654_,
        v_asyncMode_1657_,
        v___x_1659_,
    );
    v___x_1661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1661_, 0, v_o_1650_);
    crate::leanh::lean_ctor_set(v___x_1661_, 1, v_linterSets_1660_);
    v___x_1662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(
    mut v_o_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_1663_, v___y_1664_);
    crate::leanh::lean_dec(v___y_1664_);
    return v_res_1666_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(
    mut v_o_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_1667_, v___y_1669_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(
    mut v_o_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1676_ =
        l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(
            v_o_1672_,
            v___y_1673_,
            v___y_1674_,
        );
    crate::leanh::lean_dec(v___y_1674_);
    crate::leanh::lean_dec_ref(v___y_1673_);
    return v_res_1676_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
    mut v_e_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut v_unused_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1680_ = l_Lean_Expr_hasMVar(v_e_1677_);
                if v___x_1680_ == 0 {
                    v___x_1681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v_e_1677_);
                    return v___x_1681_;
                } else {
                    v___x_1682_ = lean_st_ref_get(v___y_1678_);
                    v_mctx_1683_ = crate::leanh::lean_ctor_get(v___x_1682_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1683_);
                    crate::leanh::lean_dec(v___x_1682_);
                    v___x_1684_ = l_Lean_instantiateMVarsCore(v_mctx_1683_, v_e_1677_);
                    v_fst_1685_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                    crate::leanh::lean_inc(v_fst_1685_);
                    v_snd_1686_ = crate::leanh::lean_ctor_get(v___x_1684_, 1);
                    crate::leanh::lean_inc(v_snd_1686_);
                    crate::leanh::lean_dec_ref(v___x_1684_);
                    v___x_1687_ = lean_st_ref_take(v___y_1678_);
                    v_cache_1688_ = crate::leanh::lean_ctor_get(v___x_1687_, 1);
                    v_zetaDeltaFVarIds_1689_ = crate::leanh::lean_ctor_get(v___x_1687_, 2);
                    v_postponed_1690_ = crate::leanh::lean_ctor_get(v___x_1687_, 3);
                    v_diag_1691_ = crate::leanh::lean_ctor_get(v___x_1687_, 4);
                    v_isSharedCheck_1700_ = (!crate::leanh::lean_is_exclusive(v___x_1687_)) as u8;
                    if v_isSharedCheck_1700_ == 0 {
                        v_unused_1701_ = crate::leanh::lean_ctor_get(v___x_1687_, 0);
                        crate::leanh::lean_dec(v_unused_1701_);
                        v___x_1693_ = v___x_1687_;
                        v_isShared_1694_ = v_isSharedCheck_1700_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1691_);
                        crate::leanh::lean_inc(v_postponed_1690_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1689_);
                        crate::leanh::lean_inc(v_cache_1688_);
                        crate::leanh::lean_dec(v___x_1687_);
                        v___x_1693_ = crate::leanh::lean_box(0);
                        v_isShared_1694_ = v_isSharedCheck_1700_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_snd_1686_);
                    v___x_1696_ = v___x_1693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_snd_1686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_cache_1688_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1699_,
                        2,
                        v_zetaDeltaFVarIds_1689_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_postponed_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_diag_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1697_ = lean_st_ref_set(v___y_1678_, v___x_1696_);
                v___x_1698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1698_, 0, v_fst_1685_);
                return v___x_1698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(
    mut v_e_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1705_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_e_1702_,
            v___y_1703_,
        );
    crate::leanh::lean_dec(v___y_1703_);
    return v_res_1705_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(
    mut v_e_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_e_1706_,
            v___y_1708_,
        );
    return v___x_1712_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(
    mut v_e_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1719_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(
        v_e_1713_,
        v___y_1714_,
        v___y_1715_,
        v___y_1716_,
        v___y_1717_,
    );
    crate::leanh::lean_dec(v___y_1717_);
    crate::leanh::lean_dec_ref(v___y_1716_);
    crate::leanh::lean_dec(v___y_1715_);
    crate::leanh::lean_dec_ref(v___y_1714_);
    return v_res_1719_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(
    mut v_hi_1720_: *mut crate::leanh::LeanObject,
    mut v_pivot_1721_: *mut crate::leanh::LeanObject,
    mut v_as_1722_: *mut crate::leanh::LeanObject,
    mut v_i_1723_: *mut crate::leanh::LeanObject,
    mut v_k_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1725_ = lean_nat_dec_lt(v_k_1724_, v_hi_1720_);
                if v___x_1725_ == 0 {
                    crate::leanh::lean_dec(v_k_1724_);
                    v___x_1726_ = lean_array_fswap(v_as_1722_, v_i_1723_, v_hi_1720_);
                    v___x_1727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1727_, 0, v_i_1723_);
                    crate::leanh::lean_ctor_set(v___x_1727_, 1, v___x_1726_);
                    return v___x_1727_;
                } else {
                    v___x_1728_ = lean_array_fget_borrowed(v_as_1722_, v_k_1724_);
                    v_fst_1729_ = crate::leanh::lean_ctor_get(v___x_1728_, 0);
                    v_fst_1730_ = crate::leanh::lean_ctor_get(v_pivot_1721_, 0);
                    v_start_1731_ = crate::leanh::lean_ctor_get(v_fst_1729_, 0);
                    v_start_1732_ = crate::leanh::lean_ctor_get(v_fst_1730_, 0);
                    v___x_1733_ = lean_nat_dec_lt(v_start_1731_, v_start_1732_);
                    if v___x_1733_ == 0 {
                        v___x_1734_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1735_ = lean_nat_add(v_k_1724_, v___x_1734_);
                        crate::leanh::lean_dec(v_k_1724_);
                        v_k_1724_ = v___x_1735_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1737_ = lean_array_fswap(v_as_1722_, v_i_1723_, v_k_1724_);
                        v___x_1738_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1739_ = lean_nat_add(v_i_1723_, v___x_1738_);
                        crate::leanh::lean_dec(v_i_1723_);
                        v___x_1740_ = lean_nat_add(v_k_1724_, v___x_1738_);
                        crate::leanh::lean_dec(v_k_1724_);
                        v_as_1722_ = v___x_1737_;
                        v_i_1723_ = v___x_1739_;
                        v_k_1724_ = v___x_1740_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg___boxed(
    mut v_hi_1742_: *mut crate::leanh::LeanObject,
    mut v_pivot_1743_: *mut crate::leanh::LeanObject,
    mut v_as_1744_: *mut crate::leanh::LeanObject,
    mut v_i_1745_: *mut crate::leanh::LeanObject,
    mut v_k_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1742_, v_pivot_1743_, v_as_1744_, v_i_1745_, v_k_1746_);
    crate::leanh::lean_dec_ref(v_pivot_1743_);
    crate::leanh::lean_dec(v_hi_1742_);
    return v_res_1747_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(
    mut v_x1_1748_: *mut crate::leanh::LeanObject,
    mut v_x2_1749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    v_fst_1750_ = crate::leanh::lean_ctor_get(v_x1_1748_, 0);
    v_fst_1751_ = crate::leanh::lean_ctor_get(v_x2_1749_, 0);
    v_start_1752_ = crate::leanh::lean_ctor_get(v_fst_1750_, 0);
    v_start_1753_ = crate::leanh::lean_ctor_get(v_fst_1751_, 0);
    v___x_1754_ = lean_nat_dec_lt(v_start_1752_, v_start_1753_);
    return v___x_1754_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(
    mut v_x1_1755_: *mut crate::leanh::LeanObject,
    mut v_x2_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1757_: u8 = 0;
    let mut v_r_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_1755_, v_x2_1756_);
    crate::leanh::lean_dec_ref(v_x2_1756_);
    crate::leanh::lean_dec_ref(v_x1_1755_);
    v_r_1758_ = crate::leanh::lean_box((v_res_1757_) as usize);
    return v_r_1758_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(
    mut v_n_1759_: *mut crate::leanh::LeanObject,
    mut v_as_1760_: *mut crate::leanh::LeanObject,
    mut v_lo_1761_: *mut crate::leanh::LeanObject,
    mut v_hi_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1774_ = lean_nat_dec_lt(v_lo_1761_, v_hi_1762_);
                if v___x_1774_ == 0 {
                    crate::leanh::lean_dec(v_lo_1761_);
                    return v_as_1760_;
                } else {
                    v___x_1775_ = lean_nat_add(v_lo_1761_, v_hi_1762_);
                    v___x_1776_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1777_ = lean_nat_shiftr(v___x_1775_, v___x_1776_);
                    crate::leanh::lean_dec(v___x_1775_);
                    v___x_1790_ = lean_array_fget_borrowed(v_as_1760_, v_mid_1777_);
                    v___x_1791_ = lean_array_fget_borrowed(v_as_1760_, v_lo_1761_);
                    v___x_1792_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_1790_, v___x_1791_);
                    if v___x_1792_ == 0 {
                        v___y_1785_ = v_as_1760_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1793_ = lean_array_fswap(v_as_1760_, v_lo_1761_, v_mid_1777_);
                        v___y_1785_ = v___x_1793_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1765_ = lean_array_fget(v___y_1764_, v_hi_1762_);
                crate::leanh::lean_inc_n(v_lo_1761_, 2);
                v___x_1766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1762_, v_pivot_1765_, v___y_1764_, v_lo_1761_, v_lo_1761_);
                crate::leanh::lean_dec(v_pivot_1765_);
                v_fst_1767_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                crate::leanh::lean_inc(v_fst_1767_);
                v_snd_1768_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                crate::leanh::lean_inc(v_snd_1768_);
                crate::leanh::lean_dec_ref(v___x_1766_);
                v___x_1769_ = lean_nat_dec_le(v_hi_1762_, v_fst_1767_);
                if v___x_1769_ == 0 {
                    v___x_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1759_, v_snd_1768_, v_lo_1761_, v_fst_1767_);
                    v___x_1771_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1772_ = lean_nat_add(v_fst_1767_, v___x_1771_);
                    crate::leanh::lean_dec(v_fst_1767_);
                    v_as_1760_ = v___x_1770_;
                    v_lo_1761_ = v___x_1772_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1767_);
                    crate::leanh::lean_dec(v_lo_1761_);
                    return v_snd_1768_;
                }
            }
            2 => {
                v___x_1780_ = lean_array_fget_borrowed(v___y_1779_, v_mid_1777_);
                v___x_1781_ = lean_array_fget_borrowed(v___y_1779_, v_hi_1762_);
                v___x_1782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_1780_, v___x_1781_);
                if v___x_1782_ == 0 {
                    crate::leanh::lean_dec(v_mid_1777_);
                    v___y_1764_ = v___y_1779_;
                    state = 1;
                    continue;
                } else {
                    v___x_1783_ = lean_array_fswap(v___y_1779_, v_mid_1777_, v_hi_1762_);
                    crate::leanh::lean_dec(v_mid_1777_);
                    v___y_1764_ = v___x_1783_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1786_ = lean_array_fget_borrowed(v___y_1785_, v_hi_1762_);
                v___x_1787_ = lean_array_fget_borrowed(v___y_1785_, v_lo_1761_);
                v___x_1788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_1786_, v___x_1787_);
                if v___x_1788_ == 0 {
                    v___y_1779_ = v___y_1785_;
                    state = 2;
                    continue;
                } else {
                    v___x_1789_ = lean_array_fswap(v___y_1785_, v_lo_1761_, v_hi_1762_);
                    v___y_1779_ = v___x_1789_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(
    mut v_n_1794_: *mut crate::leanh::LeanObject,
    mut v_as_1795_: *mut crate::leanh::LeanObject,
    mut v_lo_1796_: *mut crate::leanh::LeanObject,
    mut v_hi_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1794_, v_as_1795_, v_lo_1796_, v_hi_1797_);
    crate::leanh::lean_dec(v_hi_1797_);
    crate::leanh::lean_dec(v_n_1794_);
    return v_res_1798_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(
    mut v___y_1800_: u8,
    mut v_suppressElabErrors_1801_: u8,
    mut v_x_1802_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1802_) == 1 {
        let mut v_pre_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1803_ = crate::leanh::lean_ctor_get(v_x_1802_, 0);
        if crate::leanh::lean_obj_tag(v_pre_1803_) == 0 {
            let mut v_str_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1806_: u8 = 0;
            v_str_1804_ = crate::leanh::lean_ctor_get(v_x_1802_, 1);
            v___x_1805_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0;
            v___x_1806_ = lean_string_dec_eq(v_str_1804_, v___x_1805_);
            if v___x_1806_ == 0 {
                return v___y_1800_;
            } else {
                return v_suppressElabErrors_1801_;
            }
        } else {
            return v___y_1800_;
        }
    } else {
        return v___y_1800_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1808_: *mut crate::leanh::LeanObject,
    mut v_x_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21688__boxed_1810_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1811_: u8 = 0;
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21688__boxed_1810_ = (crate::leanh::lean_unbox(v___y_1807_) as u8);
    v_suppressElabErrors_boxed_1811_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1808_) as u8);
    v_res_1812_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21688__boxed_1810_, v_suppressElabErrors_boxed_1811_, v_x_1809_);
    crate::leanh::lean_dec(v_x_1809_);
    v_r_1813_ = crate::leanh::lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(
    mut v_opts_1814_: *mut crate::leanh::LeanObject,
    mut v_opt_1815_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1816_ = crate::leanh::lean_ctor_get(v_opt_1815_, 0);
    v_defValue_1817_ = crate::leanh::lean_ctor_get(v_opt_1815_, 1);
    v_map_1818_ = crate::leanh::lean_ctor_get(v_opts_1814_, 0);
    v___x_1819_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1818_,
            v_name_1816_,
        );
    if crate::leanh::lean_obj_tag(v___x_1819_) == 0 {
        let mut v___x_1820_: u8 = 0;
        v___x_1820_ = (crate::leanh::lean_unbox(v_defValue_1817_) as u8);
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1821_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
        crate::leanh::lean_inc(v_val_1821_);
        crate::leanh::lean_dec_ref_known(v___x_1819_, 1);
        if crate::leanh::lean_obj_tag(v_val_1821_) == 1 {
            let mut v_v_1822_: u8 = 0;
            v_v_1822_ = crate::leanh::lean_ctor_get_uint8(v_val_1821_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1821_, 0);
            return v_v_1822_;
        } else {
            let mut v___x_1823_: u8 = 0;
            crate::leanh::lean_dec(v_val_1821_);
            v___x_1823_ = (crate::leanh::lean_unbox(v_defValue_1817_) as u8);
            return v___x_1823_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(
    mut v_opts_1824_: *mut crate::leanh::LeanObject,
    mut v_opt_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1826_: u8 = 0;
    let mut v_r_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_1824_, v_opt_1825_);
    crate::leanh::lean_dec_ref(v_opt_1825_);
    crate::leanh::lean_dec_ref(v_opts_1824_);
    v_r_1827_ = crate::leanh::lean_box((v_res_1826_) as usize);
    return v_r_1827_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1828_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
    v___x_1830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1829_);
    return v___x_1830_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
    v___x_1832_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1833_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1833_, 0, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 1, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 2, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 3, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 4, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 5, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 6, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 7, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 8, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 9, v___x_1831_);
    return v___x_1833_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
    v___x_1836_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1836_, 0, v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = 5usize;
    v___x_1838_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1839_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1839_);
    v___x_1841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
    v___x_1842_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    crate::leanh::lean_ctor_set(v___x_1842_, 2, v___x_1838_);
    crate::leanh::lean_ctor_set(v___x_1842_, 3, v___x_1838_);
    crate::leanh::lean_ctor_set_usize(v___x_1842_, 4, v___x_1837_);
    return v___x_1842_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = crate::leanh::lean_box(1);
    v___x_1844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
    v___x_1845_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
    v___x_1846_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1846_, 0, v___x_1845_);
    crate::leanh::lean_ctor_set(v___x_1846_, 1, v___x_1844_);
    crate::leanh::lean_ctor_set(v___x_1846_, 2, v___x_1843_);
    return v___x_1846_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(
    mut v_msgData_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = lean_st_ref_get(v___y_1848_);
    v_env_1851_ = crate::leanh::lean_ctor_get(v___x_1850_, 0);
    crate::leanh::lean_inc_ref(v_env_1851_);
    crate::leanh::lean_dec(v___x_1850_);
    v___x_1852_ = lean_st_ref_get(v___y_1848_);
    v_scopes_1853_ = crate::leanh::lean_ctor_get(v___x_1852_, 2);
    crate::leanh::lean_inc(v_scopes_1853_);
    crate::leanh::lean_dec(v___x_1852_);
    v___x_1854_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1855_ = l_List_head_x21___redArg(v___x_1854_, v_scopes_1853_);
    crate::leanh::lean_dec(v_scopes_1853_);
    v_opts_1856_ = crate::leanh::lean_ctor_get(v___x_1855_, 1);
    crate::leanh::lean_inc_ref(v_opts_1856_);
    crate::leanh::lean_dec(v___x_1855_);
    v___x_1857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
    v___x_1858_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
    v___x_1859_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1859_, 0, v_env_1851_);
    crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1857_);
    crate::leanh::lean_ctor_set(v___x_1859_, 2, v___x_1858_);
    crate::leanh::lean_ctor_set(v___x_1859_, 3, v_opts_1856_);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 1, v_msgData_1847_);
    v___x_1861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(
    mut v_msgData_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1862_, v___y_1863_);
    crate::leanh::lean_dec(v___y_1863_);
    return v_res_1865_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(
    mut v_ref_1867_: *mut crate::leanh::LeanObject,
    mut v_msgData_1868_: *mut crate::leanh::LeanObject,
    mut v_severity_1869_: u8,
    mut v_isSilent_1870_: u8,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: u8 = 0;
    let mut v___y_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: u8 = 0;
    let mut v___y_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v_a_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v_a_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v___y_1938_: u8 = 0;
    let mut v___y_1939_: u8 = 0;
    let mut v___y_1940_: u8 = 0;
    let mut v___y_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1945_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v___y_1966_: u8 = 0;
    let mut v___y_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: u8 = 0;
    let mut v___y_1969_: u8 = 0;
    let mut v___y_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: u8 = 0;
    let mut v___y_1975_: u8 = 0;
    let mut v___y_1976_: u8 = 0;
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v___x_1991_: u8 = 0;
    let mut v___y_1993_: u8 = 0;
    let mut v___y_1994_: u8 = 0;
    let mut v___y_1995_: u8 = 0;
    let mut v___y_1997_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1991_ = 2;
                v___x_2009_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1869_, v___x_1991_);
                if v___x_2009_ == 0 {
                    v___y_1997_ = v___x_2009_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1868_);
                    v___x_2010_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1868_);
                    v___y_1997_ = v___x_2010_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1883_ = l_Lean_Elab_Command_getScope___redArg(v___y_1882_);
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_a_1884_);
                    crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                    v___x_1885_ = l_Lean_Elab_Command_getScope___redArg(v___y_1882_);
                    if crate::leanh::lean_obj_tag(v___x_1885_) == 0 {
                        v_a_1886_ = crate::leanh::lean_ctor_get(v___x_1885_, 0);
                        v_isSharedCheck_1920_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1885_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1888_ = v___x_1885_;
                            v_isShared_1889_ = v_isSharedCheck_1920_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1886_);
                            crate::leanh::lean_dec(v___x_1885_);
                            v___x_1888_ = crate::leanh::lean_box(0);
                            v_isShared_1889_ = v_isSharedCheck_1920_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1884_);
                        crate::leanh::lean_dec(v___y_1880_);
                        crate::leanh::lean_dec_ref(v___y_1878_);
                        crate::leanh::lean_dec_ref(v___y_1876_);
                        v_a_1921_ = crate::leanh::lean_ctor_get(v___x_1885_, 0);
                        v_isSharedCheck_1928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1885_)) as u8;
                        if v_isSharedCheck_1928_ == 0 {
                            v___x_1923_ = v___x_1885_;
                            v_isShared_1924_ = v_isSharedCheck_1928_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1921_);
                            crate::leanh::lean_dec(v___x_1885_);
                            v___x_1923_ = crate::leanh::lean_box(0);
                            v_isShared_1924_ = v_isSharedCheck_1928_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1880_);
                    crate::leanh::lean_dec_ref(v___y_1878_);
                    crate::leanh::lean_dec_ref(v___y_1876_);
                    v_a_1929_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1936_ = (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1931_ = v___x_1883_;
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1929_);
                        crate::leanh::lean_dec(v___x_1883_);
                        v___x_1931_ = crate::leanh::lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1890_ = lean_st_ref_take(v___y_1882_);
                v_currNamespace_1891_ = crate::leanh::lean_ctor_get(v_a_1884_, 2);
                crate::leanh::lean_inc(v_currNamespace_1891_);
                crate::leanh::lean_dec(v_a_1884_);
                v_openDecls_1892_ = crate::leanh::lean_ctor_get(v_a_1886_, 3);
                crate::leanh::lean_inc(v_openDecls_1892_);
                crate::leanh::lean_dec(v_a_1886_);
                v_env_1893_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                v_messages_1894_ = crate::leanh::lean_ctor_get(v___x_1890_, 1);
                v_scopes_1895_ = crate::leanh::lean_ctor_get(v___x_1890_, 2);
                v_usedQuotCtxts_1896_ = crate::leanh::lean_ctor_get(v___x_1890_, 3);
                v_nextMacroScope_1897_ = crate::leanh::lean_ctor_get(v___x_1890_, 4);
                v_maxRecDepth_1898_ = crate::leanh::lean_ctor_get(v___x_1890_, 5);
                v_ngen_1899_ = crate::leanh::lean_ctor_get(v___x_1890_, 6);
                v_auxDeclNGen_1900_ = crate::leanh::lean_ctor_get(v___x_1890_, 7);
                v_infoState_1901_ = crate::leanh::lean_ctor_get(v___x_1890_, 8);
                v_traceState_1902_ = crate::leanh::lean_ctor_get(v___x_1890_, 9);
                v_snapshotTasks_1903_ = crate::leanh::lean_ctor_get(v___x_1890_, 10);
                v_isSharedCheck_1919_ = (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1905_ = v___x_1890_;
                    v_isShared_1906_ = v_isSharedCheck_1919_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1903_);
                    crate::leanh::lean_inc(v_traceState_1902_);
                    crate::leanh::lean_inc(v_infoState_1901_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1900_);
                    crate::leanh::lean_inc(v_ngen_1899_);
                    crate::leanh::lean_inc(v_maxRecDepth_1898_);
                    crate::leanh::lean_inc(v_nextMacroScope_1897_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1896_);
                    crate::leanh::lean_inc(v_scopes_1895_);
                    crate::leanh::lean_inc(v_messages_1894_);
                    crate::leanh::lean_inc(v_env_1893_);
                    crate::leanh::lean_dec(v___x_1890_);
                    v___x_1905_ = crate::leanh::lean_box(0);
                    v_isShared_1906_ = v_isSharedCheck_1919_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1907_, 0, v_currNamespace_1891_);
                crate::leanh::lean_ctor_set(v___x_1907_, 1, v_openDecls_1892_);
                v___x_1908_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
                crate::leanh::lean_ctor_set(v___x_1908_, 1, v___y_1878_);
                crate::leanh::lean_inc_ref(v___y_1875_);
                crate::leanh::lean_inc_ref(v___y_1877_);
                v___x_1909_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1909_, 0, v___y_1877_);
                crate::leanh::lean_ctor_set(v___x_1909_, 1, v___y_1876_);
                crate::leanh::lean_ctor_set(v___x_1909_, 2, v___y_1880_);
                crate::leanh::lean_ctor_set(v___x_1909_, 3, v___y_1875_);
                crate::leanh::lean_ctor_set(v___x_1909_, 4, v___x_1908_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1879_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1881_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1870_,
                );
                v___x_1910_ = l_Lean_MessageLog_add(v___x_1909_, v_messages_1894_);
                if v_isShared_1906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1910_);
                    v___x_1912_ = v___x_1905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_scopes_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_usedQuotCtxts_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_nextMacroScope_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_maxRecDepth_1898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_ngen_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_auxDeclNGen_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_infoState_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 9, v_traceState_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 10, v_snapshotTasks_1903_);
                    v___x_1912_ = v_reuseFailAlloc_1918_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1913_ = lean_st_ref_set(v___y_1882_, v___x_1912_);
                v___x_1914_ = crate::leanh::lean_box(0);
                if v_isShared_1889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1888_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1916_;
            }
            6 => {
                if v_isShared_1924_ == 0 {
                    v___x_1926_ = v___x_1923_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
                    v___x_1926_ = v_reuseFailAlloc_1927_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1926_;
            }
            8 => {
                if v_isShared_1932_ == 0 {
                    v___x_1934_ = v___x_1931_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
                    v___x_1934_ = v_reuseFailAlloc_1935_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1934_;
            }
            10 => {
                v_fileName_1943_ = crate::leanh::lean_ctor_get(v___y_1871_, 0);
                v_fileMap_1944_ = crate::leanh::lean_ctor_get(v___y_1871_, 1);
                v_suppressElabErrors_1945_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_1946_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1868_,
                    );
                v___x_1947_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_1946_, v___y_1872_);
                v_a_1948_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                v_isSharedCheck_1964_ = (!crate::leanh::lean_is_exclusive(v___x_1947_)) as u8;
                if v_isSharedCheck_1964_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    v_isShared_1951_ = v_isSharedCheck_1964_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1948_);
                    crate::leanh::lean_dec(v___x_1947_);
                    v___x_1950_ = crate::leanh::lean_box(0);
                    v_isShared_1951_ = v_isSharedCheck_1964_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1944_, 2);
                v___x_1952_ = l_Lean_FileMap_toPosition(v_fileMap_1944_, v___y_1941_);
                crate::leanh::lean_dec(v___y_1941_);
                v___x_1953_ = l_Lean_FileMap_toPosition(v_fileMap_1944_, v___y_1942_);
                crate::leanh::lean_dec(v___y_1942_);
                v___x_1954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                v___x_1955_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0;
                if v_suppressElabErrors_1945_ == 0 {
                    crate::leanh::lean_del_object(v___x_1950_);
                    v___y_1875_ = v___x_1955_;
                    v___y_1876_ = v___x_1952_;
                    v___y_1877_ = v_fileName_1943_;
                    v___y_1878_ = v_a_1948_;
                    v___y_1879_ = v___y_1939_;
                    v___y_1880_ = v___x_1954_;
                    v___y_1881_ = v___y_1940_;
                    v___y_1882_ = v___y_1872_;
                    state = 1;
                    continue;
                } else {
                    v___x_1956_ = crate::leanh::lean_box((v___y_1938_) as usize);
                    v___x_1957_ = crate::leanh::lean_box((v_suppressElabErrors_1945_) as usize);
                    v___f_1958_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1958_, 0, v___x_1956_);
                    crate::leanh::lean_closure_set(v___f_1958_, 1, v___x_1957_);
                    crate::leanh::lean_inc(v_a_1948_);
                    v___x_1959_ = l_Lean_MessageData_hasTag(v___f_1958_, v_a_1948_);
                    if v___x_1959_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1954_, 1);
                        crate::leanh::lean_dec_ref(v___x_1952_);
                        crate::leanh::lean_dec(v_a_1948_);
                        v___x_1960_ = crate::leanh::lean_box(0);
                        if v_isShared_1951_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1960_);
                            v___x_1962_ = v___x_1950_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1963_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
                            v___x_1962_ = v_reuseFailAlloc_1963_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1950_);
                        v___y_1875_ = v___x_1955_;
                        v___y_1876_ = v___x_1952_;
                        v___y_1877_ = v_fileName_1943_;
                        v___y_1878_ = v_a_1948_;
                        v___y_1879_ = v___y_1939_;
                        v___y_1880_ = v___x_1954_;
                        v___y_1881_ = v___y_1940_;
                        v___y_1882_ = v___y_1872_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1962_;
            }
            13 => {
                v___x_1971_ = l_Lean_Syntax_getTailPos_x3f(v___y_1967_, v___y_1968_);
                crate::leanh::lean_dec(v___y_1967_);
                if crate::leanh::lean_obj_tag(v___x_1971_) == 0 {
                    crate::leanh::lean_inc(v___y_1970_);
                    v___y_1938_ = v___y_1966_;
                    v___y_1939_ = v___y_1968_;
                    v___y_1940_ = v___y_1969_;
                    v___y_1941_ = v___y_1970_;
                    v___y_1942_ = v___y_1970_;
                    state = 10;
                    continue;
                } else {
                    v_val_1972_ = crate::leanh::lean_ctor_get(v___x_1971_, 0);
                    crate::leanh::lean_inc(v_val_1972_);
                    crate::leanh::lean_dec_ref_known(v___x_1971_, 1);
                    v___y_1938_ = v___y_1966_;
                    v___y_1939_ = v___y_1968_;
                    v___y_1940_ = v___y_1969_;
                    v___y_1941_ = v___y_1970_;
                    v___y_1942_ = v_val_1972_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1977_ = l_Lean_Elab_Command_getRef___redArg(v___y_1871_);
                if crate::leanh::lean_obj_tag(v___x_1977_) == 0 {
                    v_a_1978_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
                    crate::leanh::lean_inc(v_a_1978_);
                    crate::leanh::lean_dec_ref_known(v___x_1977_, 1);
                    v_ref_1979_ = l_Lean_replaceRef(v_ref_1867_, v_a_1978_);
                    crate::leanh::lean_dec(v_a_1978_);
                    v___x_1980_ = l_Lean_Syntax_getPos_x3f(v_ref_1979_, v___y_1975_);
                    if crate::leanh::lean_obj_tag(v___x_1980_) == 0 {
                        v___x_1981_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_1966_ = v___y_1974_;
                        v___y_1967_ = v_ref_1979_;
                        v___y_1968_ = v___y_1975_;
                        v___y_1969_ = v___y_1976_;
                        v___y_1970_ = v___x_1981_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1982_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                        crate::leanh::lean_inc(v_val_1982_);
                        crate::leanh::lean_dec_ref_known(v___x_1980_, 1);
                        v___y_1966_ = v___y_1974_;
                        v___y_1967_ = v_ref_1979_;
                        v___y_1968_ = v___y_1975_;
                        v___y_1969_ = v___y_1976_;
                        v___y_1970_ = v_val_1982_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1868_);
                    v_a_1983_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
                    v_isSharedCheck_1990_ = (!crate::leanh::lean_is_exclusive(v___x_1977_)) as u8;
                    if v_isSharedCheck_1990_ == 0 {
                        v___x_1985_ = v___x_1977_;
                        v_isShared_1986_ = v_isSharedCheck_1990_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1983_);
                        crate::leanh::lean_dec(v___x_1977_);
                        v___x_1985_ = crate::leanh::lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_1990_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1986_ == 0 {
                    v___x_1988_ = v___x_1985_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1988_;
            }
            17 => {
                if v___y_1995_ == 0 {
                    v___y_1974_ = v___y_1993_;
                    v___y_1975_ = v___y_1994_;
                    v___y_1976_ = v_severity_1869_;
                    state = 14;
                    continue;
                } else {
                    v___y_1974_ = v___y_1993_;
                    v___y_1975_ = v___y_1994_;
                    v___y_1976_ = v___x_1991_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1997_ == 0 {
                    v___x_1998_ = lean_st_ref_get(v___y_1872_);
                    v_scopes_1999_ = crate::leanh::lean_ctor_get(v___x_1998_, 2);
                    crate::leanh::lean_inc(v_scopes_1999_);
                    crate::leanh::lean_dec(v___x_1998_);
                    v___x_2000_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2001_ = l_List_head_x21___redArg(v___x_2000_, v_scopes_1999_);
                    crate::leanh::lean_dec(v_scopes_1999_);
                    v_opts_2002_ = crate::leanh::lean_ctor_get(v___x_2001_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2002_);
                    crate::leanh::lean_dec(v___x_2001_);
                    v___x_2003_ = 1;
                    v___x_2004_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1869_, v___x_2003_);
                    if v___x_2004_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2002_);
                        v___y_1993_ = v___y_1997_;
                        v___y_1994_ = v___y_1997_;
                        v___y_1995_ = v___x_2004_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2005_ = l_Lean_warningAsError;
                        v___x_2006_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_2002_, v___x_2005_);
                        crate::leanh::lean_dec_ref(v_opts_2002_);
                        v___y_1993_ = v___y_1997_;
                        v___y_1994_ = v___y_1997_;
                        v___y_1995_ = v___x_2006_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1868_);
                    v___x_2007_ = crate::leanh::lean_box(0);
                    v___x_2008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2008_, 0, v___x_2007_);
                    return v___x_2008_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(
    mut v_ref_2011_: *mut crate::leanh::LeanObject,
    mut v_msgData_2012_: *mut crate::leanh::LeanObject,
    mut v_severity_2013_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2018_: u8 = 0;
    let mut v_isSilent_boxed_2019_: u8 = 0;
    let mut v_res_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2018_ = (crate::leanh::lean_unbox(v_severity_2013_) as u8);
    v_isSilent_boxed_2019_ = (crate::leanh::lean_unbox(v_isSilent_2014_) as u8);
    v_res_2020_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_2011_, v_msgData_2012_, v_severity_boxed_2018_, v_isSilent_boxed_2019_, v___y_2015_, v___y_2016_);
    crate::leanh::lean_dec(v___y_2016_);
    crate::leanh::lean_dec_ref(v___y_2015_);
    crate::leanh::lean_dec(v_ref_2011_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(
    mut v_ref_2021_: *mut crate::leanh::LeanObject,
    mut v_msgData_2022_: *mut crate::leanh::LeanObject,
    mut v___y_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2026_ = 1;
    v___x_2027_ = 0;
    v___x_2028_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_2021_, v_msgData_2022_, v___x_2026_, v___x_2027_, v___y_2023_, v___y_2024_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(
    mut v_ref_2029_: *mut crate::leanh::LeanObject,
    mut v_msgData_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2034_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_2029_, v_msgData_2030_, v___y_2031_, v___y_2032_);
    crate::leanh::lean_dec(v___y_2032_);
    crate::leanh::lean_dec_ref(v___y_2031_);
    crate::leanh::lean_dec(v_ref_2029_);
    return v_res_2034_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0;
    v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2039_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2;
    v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
    return v___x_2040_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
    mut v_linterOption_2041_: *mut crate::leanh::LeanObject,
    mut v_stx_2042_: *mut crate::leanh::LeanObject,
    mut v_msg_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_unused_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2047_ = crate::leanh::lean_ctor_get(v_linterOption_2041_, 0);
                v_isSharedCheck_2064_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_2041_)) as u8;
                if v_isSharedCheck_2064_ == 0 {
                    v_unused_2065_ = crate::leanh::lean_ctor_get(v_linterOption_2041_, 1);
                    crate::leanh::lean_dec(v_unused_2065_);
                    v___x_2049_ = v_linterOption_2041_;
                    v_isShared_2050_ = v_isSharedCheck_2064_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2047_);
                    crate::leanh::lean_dec(v_linterOption_2041_);
                    v___x_2049_ = crate::leanh::lean_box(0);
                    v_isShared_2050_ = v_isSharedCheck_2064_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2051_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
                crate::leanh::lean_inc(v_name_2047_);
                v___x_2052_ = l_Lean_MessageData_ofName(v_name_2047_);
                if v_isShared_2050_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2049_, 7);
                    crate::leanh::lean_ctor_set(v___x_2049_, 1, v___x_2052_);
                    crate::leanh::lean_ctor_set(v___x_2049_, 0, v___x_2051_);
                    v___x_2054_ = v___x_2049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2052_);
                    v___x_2054_ = v_reuseFailAlloc_2063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2055_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
                v___x_2056_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2054_);
                crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
                v_disable_2057_ = l_Lean_MessageData_note(v___x_2056_);
                v___x_2058_ = l_Lean_Linter_linterMessageTag;
                v___x_2059_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2059_, 0, v_msg_2043_);
                crate::leanh::lean_ctor_set(v___x_2059_, 1, v_disable_2057_);
                v___x_2060_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2058_);
                crate::leanh::lean_ctor_set(v___x_2060_, 1, v___x_2059_);
                v___x_2061_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2061_, 0, v_name_2047_);
                crate::leanh::lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                v___x_2062_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_2042_, v___x_2061_, v___y_2044_, v___y_2045_);
                return v___x_2062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(
    mut v_linterOption_2066_: *mut crate::leanh::LeanObject,
    mut v_stx_2067_: *mut crate::leanh::LeanObject,
    mut v_msg_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
        v_linterOption_2066_,
        v_stx_2067_,
        v_msg_2068_,
        v___y_2069_,
        v___y_2070_,
    );
    crate::leanh::lean_dec(v___y_2070_);
    crate::leanh::lean_dec_ref(v___y_2069_);
    crate::leanh::lean_dec(v_stx_2067_);
    return v_res_2072_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0;
    v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2;
    v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
    return v___x_2078_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4;
    v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
    return v___x_2081_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6;
    v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
    return v___x_2084_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8;
    v___x_2087_ = l_Lean_stringToMessageData(v___x_2086_);
    return v___x_2087_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10;
    v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(
    mut v_as_2091_: *mut crate::leanh::LeanObject,
    mut v_sz_2092_: usize,
    mut v_i_2093_: usize,
    mut v_b_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v_snd_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_fst_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: usize = 0;
    let mut v___x_2139_: usize = 0;
    let mut v_reuseFailAlloc_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_unused_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2098_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
                if v___x_2098_ == 0 {
                    v___x_2099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2099_, 0, v_b_2094_);
                    return v___x_2099_;
                } else {
                    v_a_2100_ = lean_array_uget(v_as_2091_, v_i_2093_);
                    v_snd_2101_ = crate::leanh::lean_ctor_get(v_a_2100_, 1);
                    v_isSharedCheck_2146_ = (!crate::leanh::lean_is_exclusive(v_a_2100_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v_unused_2147_ = crate::leanh::lean_ctor_get(v_a_2100_, 0);
                        crate::leanh::lean_dec(v_unused_2147_);
                        v___x_2103_ = v_a_2100_;
                        v_isShared_2104_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2101_);
                        crate::leanh::lean_dec(v_a_2100_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2105_ = crate::leanh::lean_ctor_get(v_snd_2101_, 1);
                v_fst_2106_ = crate::leanh::lean_ctor_get(v_snd_2101_, 0);
                v_isSharedCheck_2145_ = (!crate::leanh::lean_is_exclusive(v_snd_2101_)) as u8;
                if v_isSharedCheck_2145_ == 0 {
                    v___x_2108_ = v_snd_2101_;
                    v_isShared_2109_ = v_isSharedCheck_2145_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2105_);
                    crate::leanh::lean_inc(v_fst_2106_);
                    crate::leanh::lean_dec(v_snd_2101_);
                    v___x_2108_ = crate::leanh::lean_box(0);
                    v_isShared_2109_ = v_isSharedCheck_2145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_2110_ = crate::leanh::lean_ctor_get(v_snd_2105_, 0);
                v_snd_2111_ = crate::leanh::lean_ctor_get(v_snd_2105_, 1);
                v_isSharedCheck_2144_ = (!crate::leanh::lean_is_exclusive(v_snd_2105_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2113_ = v_snd_2105_;
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2111_);
                    crate::leanh::lean_inc(v_fst_2110_);
                    crate::leanh::lean_dec(v_snd_2105_);
                    v___x_2113_ = crate::leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2115_ = l_Lean_Linter_linter_constructorNameAsVariable;
                v___x_2116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
                v___x_2117_ = l_Lean_MessageData_ofName(v_fst_2110_);
                crate::leanh::lean_inc_ref(v___x_2117_);
                if v_isShared_2114_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2113_, 7);
                    crate::leanh::lean_ctor_set(v___x_2113_, 1, v___x_2117_);
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2116_);
                    v___x_2119_ = v___x_2113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2117_);
                    v___x_2119_ = v_reuseFailAlloc_2143_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
                if v_isShared_2109_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2108_, 7);
                    crate::leanh::lean_ctor_set(v___x_2108_, 1, v___x_2120_);
                    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2119_);
                    v___x_2122_ = v___x_2108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2123_ = l_Lean_MessageData_ofName(v_snd_2111_);
                crate::leanh::lean_inc_ref(v___x_2123_);
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2103_, 7);
                    crate::leanh::lean_ctor_set(v___x_2103_, 1, v___x_2123_);
                    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2122_);
                    v___x_2125_ = v___x_2103_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2123_);
                    v___x_2125_ = v_reuseFailAlloc_2141_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2126_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
                v___x_2127_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2125_);
                crate::leanh::lean_ctor_set(v___x_2127_, 1, v___x_2126_);
                v___x_2128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
                v___x_2129_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2129_, 0, v___x_2128_);
                crate::leanh::lean_ctor_set(v___x_2129_, 1, v___x_2117_);
                v___x_2130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
                v___x_2131_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2131_, 0, v___x_2129_);
                crate::leanh::lean_ctor_set(v___x_2131_, 1, v___x_2130_);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2123_);
                v___x_2133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
                v___x_2134_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2134_, 0, v___x_2132_);
                crate::leanh::lean_ctor_set(v___x_2134_, 1, v___x_2133_);
                v___x_2135_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2127_);
                crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                v___x_2136_ =
                    l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
                        v___x_2115_,
                        v_fst_2106_,
                        v___x_2135_,
                        v___y_2095_,
                        v___y_2096_,
                    );
                crate::leanh::lean_dec(v_fst_2106_);
                if crate::leanh::lean_obj_tag(v___x_2136_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2136_, 1);
                    v___x_2137_ = crate::leanh::lean_box(0);
                    v___x_2138_ = 1usize;
                    v___x_2139_ = lean_usize_add(v_i_2093_, v___x_2138_);
                    v_i_2093_ = v___x_2139_;
                    v_b_2094_ = v___x_2137_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2136_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(
    mut v_as_2148_: *mut crate::leanh::LeanObject,
    mut v_sz_2149_: *mut crate::leanh::LeanObject,
    mut v_i_2150_: *mut crate::leanh::LeanObject,
    mut v_b_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2155_: usize = 0;
    let mut v_i_boxed_2156_: usize = 0;
    let mut v_res_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2155_ = crate::leanh::lean_unbox_usize(v_sz_2149_);
    crate::leanh::lean_dec(v_sz_2149_);
    v_i_boxed_2156_ = crate::leanh::lean_unbox_usize(v_i_2150_);
    crate::leanh::lean_dec(v_i_2150_);
    v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_2148_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2151_, v___y_2152_, v___y_2153_);
    crate::leanh::lean_dec(v___y_2153_);
    crate::leanh::lean_dec_ref(v___y_2152_);
    crate::leanh::lean_dec_ref(v_as_2148_);
    return v_res_2157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(
    mut v___x_2158_: u8,
    mut v_x_2159_: *mut crate::leanh::LeanObject,
    mut v_x_2160_: *mut crate::leanh::LeanObject,
    mut v_x_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = crate::leanh::lean_box((v___x_2158_) as usize);
    v___x_2166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(
    mut v___x_2167_: *mut crate::leanh::LeanObject,
    mut v_x_2168_: *mut crate::leanh::LeanObject,
    mut v_x_2169_: *mut crate::leanh::LeanObject,
    mut v_x_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_22304__boxed_2174_: u8 = 0;
    let mut v_res_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22304__boxed_2174_ = (crate::leanh::lean_unbox(v___x_2167_) as u8);
    v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22304__boxed_2174_, v_x_2168_, v_x_2169_, v_x_2170_, v___y_2171_, v___y_2172_);
    crate::leanh::lean_dec(v___y_2172_);
    crate::leanh::lean_dec_ref(v___y_2171_);
    crate::leanh::lean_dec_ref(v_x_2170_);
    crate::leanh::lean_dec_ref(v_x_2169_);
    crate::leanh::lean_dec_ref(v_x_2168_);
    return v_res_2175_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(
    mut v_a_2176_: *mut crate::leanh::LeanObject,
    mut v_x_2177_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2178_: u8 = 0;
    let mut v_key_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2177_) == 0 {
                    v___x_2178_ = 0;
                    return v___x_2178_;
                } else {
                    v_key_2179_ = crate::leanh::lean_ctor_get(v_x_2177_, 0);
                    v_tail_2180_ = crate::leanh::lean_ctor_get(v_x_2177_, 2);
                    v___x_2181_ = l_Lean_Syntax_instBEqRange_beq(v_key_2179_, v_a_2176_);
                    if v___x_2181_ == 0 {
                        v_x_2177_ = v_tail_2180_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2181_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_x_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_2183_, v_x_2184_);
    crate::leanh::lean_dec(v_x_2184_);
    crate::leanh::lean_dec_ref(v_a_2183_);
    v_r_2186_ = crate::leanh::lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(
    mut v_m_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u64 = 0;
    let mut v___x_2192_: u64 = 0;
    let mut v___x_2193_: u64 = 0;
    let mut v_fold_2194_: u64 = 0;
    let mut v___x_2195_: u64 = 0;
    let mut v___x_2196_: u64 = 0;
    let mut v___x_2197_: u64 = 0;
    let mut v___x_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: usize = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    v_buckets_2189_ = crate::leanh::lean_ctor_get(v_m_2187_, 1);
    v___x_2190_ = lean_array_get_size(v_buckets_2189_);
    v___x_2191_ = l_Lean_Syntax_instHashableRange_hash(v_a_2188_);
    v___x_2192_ = 32u64;
    v___x_2193_ = lean_uint64_shift_right(v___x_2191_, v___x_2192_);
    v_fold_2194_ = lean_uint64_xor(v___x_2191_, v___x_2193_);
    v___x_2195_ = 16u64;
    v___x_2196_ = lean_uint64_shift_right(v_fold_2194_, v___x_2195_);
    v___x_2197_ = lean_uint64_xor(v_fold_2194_, v___x_2196_);
    v___x_2198_ = lean_uint64_to_usize(v___x_2197_);
    v___x_2199_ = lean_usize_of_nat(v___x_2190_);
    v___x_2200_ = 1usize;
    v___x_2201_ = lean_usize_sub(v___x_2199_, v___x_2200_);
    v___x_2202_ = lean_usize_land(v___x_2198_, v___x_2201_);
    v___x_2203_ = lean_array_uget_borrowed(v_buckets_2189_, v___x_2202_);
    v___x_2204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_2188_, v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(
    mut v_m_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2207_: u8 = 0;
    let mut v_r_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_2205_, v_a_2206_);
    crate::leanh::lean_dec_ref(v_a_2206_);
    crate::leanh::lean_dec_ref(v_m_2205_);
    v_r_2208_ = crate::leanh::lean_box((v_res_2207_) as usize);
    return v_r_2208_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(
    mut v_a_2209_: *mut crate::leanh::LeanObject,
    mut v_b_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2211_) == 0 {
                    crate::leanh::lean_dec(v_b_2210_);
                    crate::leanh::lean_dec_ref(v_a_2209_);
                    return v_x_2211_;
                } else {
                    v_key_2212_ = crate::leanh::lean_ctor_get(v_x_2211_, 0);
                    v_value_2213_ = crate::leanh::lean_ctor_get(v_x_2211_, 1);
                    v_tail_2214_ = crate::leanh::lean_ctor_get(v_x_2211_, 2);
                    v_isSharedCheck_2226_ = (!crate::leanh::lean_is_exclusive(v_x_2211_)) as u8;
                    if v_isSharedCheck_2226_ == 0 {
                        v___x_2216_ = v_x_2211_;
                        v_isShared_2217_ = v_isSharedCheck_2226_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2214_);
                        crate::leanh::lean_inc(v_value_2213_);
                        crate::leanh::lean_inc(v_key_2212_);
                        crate::leanh::lean_dec(v_x_2211_);
                        v___x_2216_ = crate::leanh::lean_box(0);
                        v_isShared_2217_ = v_isSharedCheck_2226_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2218_ = l_Lean_Syntax_instBEqRange_beq(v_key_2212_, v_a_2209_);
                if v___x_2218_ == 0 {
                    v___x_2219_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_2209_, v_b_2210_, v_tail_2214_);
                    if v_isShared_2217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2216_, 2, v___x_2219_);
                        v___x_2221_ = v___x_2216_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2222_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_key_2212_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_value_2213_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2219_);
                        v___x_2221_ = v_reuseFailAlloc_2222_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2213_);
                    crate::leanh::lean_dec(v_key_2212_);
                    if v_isShared_2217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2216_, 1, v_b_2210_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 0, v_a_2209_);
                        v___x_2224_ = v___x_2216_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2225_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2209_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_b_2210_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_tail_2214_);
                        v___x_2224_ = v_reuseFailAlloc_2225_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2221_;
            }
            3 => {
                return v___x_2224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(
    mut v_x_2227_: *mut crate::leanh::LeanObject,
    mut v_x_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u64 = 0;
    let mut v___x_2237_: u64 = 0;
    let mut v___x_2238_: u64 = 0;
    let mut v_fold_2239_: u64 = 0;
    let mut v___x_2240_: u64 = 0;
    let mut v___x_2241_: u64 = 0;
    let mut v___x_2242_: u64 = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: usize = 0;
    let mut v___x_2246_: usize = 0;
    let mut v___x_2247_: usize = 0;
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2228_) == 0 {
                    return v_x_2227_;
                } else {
                    v_key_2229_ = crate::leanh::lean_ctor_get(v_x_2228_, 0);
                    v_value_2230_ = crate::leanh::lean_ctor_get(v_x_2228_, 1);
                    v_tail_2231_ = crate::leanh::lean_ctor_get(v_x_2228_, 2);
                    v_isSharedCheck_2254_ = (!crate::leanh::lean_is_exclusive(v_x_2228_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2233_ = v_x_2228_;
                        v_isShared_2234_ = v_isSharedCheck_2254_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2231_);
                        crate::leanh::lean_inc(v_value_2230_);
                        crate::leanh::lean_inc(v_key_2229_);
                        crate::leanh::lean_dec(v_x_2228_);
                        v___x_2233_ = crate::leanh::lean_box(0);
                        v_isShared_2234_ = v_isSharedCheck_2254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2235_ = lean_array_get_size(v_x_2227_);
                v___x_2236_ = l_Lean_Syntax_instHashableRange_hash(v_key_2229_);
                v___x_2237_ = 32u64;
                v___x_2238_ = lean_uint64_shift_right(v___x_2236_, v___x_2237_);
                v_fold_2239_ = lean_uint64_xor(v___x_2236_, v___x_2238_);
                v___x_2240_ = 16u64;
                v___x_2241_ = lean_uint64_shift_right(v_fold_2239_, v___x_2240_);
                v___x_2242_ = lean_uint64_xor(v_fold_2239_, v___x_2241_);
                v___x_2243_ = lean_uint64_to_usize(v___x_2242_);
                v___x_2244_ = lean_usize_of_nat(v___x_2235_);
                v___x_2245_ = 1usize;
                v___x_2246_ = lean_usize_sub(v___x_2244_, v___x_2245_);
                v___x_2247_ = lean_usize_land(v___x_2243_, v___x_2246_);
                v___x_2248_ = lean_array_uget_borrowed(v_x_2227_, v___x_2247_);
                crate::leanh::lean_inc(v___x_2248_);
                if v_isShared_2234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2233_, 2, v___x_2248_);
                    v___x_2250_ = v___x_2233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_key_2229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_value_2230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 2, v___x_2248_);
                    v___x_2250_ = v_reuseFailAlloc_2253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2251_ = lean_array_uset(v_x_2227_, v___x_2247_, v___x_2250_);
                v_x_2227_ = v___x_2251_;
                v_x_2228_ = v_tail_2231_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(
    mut v_i_2255_: *mut crate::leanh::LeanObject,
    mut v_source_2256_: *mut crate::leanh::LeanObject,
    mut v_target_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v_es_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_array_get_size(v_source_2256_);
                v___x_2259_ = lean_nat_dec_lt(v_i_2255_, v___x_2258_);
                if v___x_2259_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2256_);
                    crate::leanh::lean_dec(v_i_2255_);
                    return v_target_2257_;
                } else {
                    v_es_2260_ = lean_array_fget(v_source_2256_, v_i_2255_);
                    v___x_2261_ = crate::leanh::lean_box(0);
                    v_source_2262_ = lean_array_fset(v_source_2256_, v_i_2255_, v___x_2261_);
                    v_target_2263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_2257_, v_es_2260_);
                    v___x_2264_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2265_ = lean_nat_add(v_i_2255_, v___x_2264_);
                    crate::leanh::lean_dec(v_i_2255_);
                    v_i_2255_ = v___x_2265_;
                    v_source_2256_ = v_source_2262_;
                    v_target_2257_ = v_target_2263_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(
    mut v_data_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = lean_array_get_size(v_data_2267_);
    v___x_2269_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2270_ = lean_nat_mul(v___x_2268_, v___x_2269_);
    v___x_2271_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2272_ = crate::leanh::lean_box(0);
    v___x_2273_ = lean_mk_array(v_nbuckets_2270_, v___x_2272_);
    v___x_2274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_2271_, v_data_2267_, v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(
    mut v_m_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
    mut v_b_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u64 = 0;
    let mut v___x_2285_: u64 = 0;
    let mut v___x_2286_: u64 = 0;
    let mut v_fold_2287_: u64 = 0;
    let mut v___x_2288_: u64 = 0;
    let mut v___x_2289_: u64 = 0;
    let mut v___x_2290_: u64 = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut v_bkt_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v_val_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2278_ = crate::leanh::lean_ctor_get(v_m_2275_, 0);
                v_buckets_2279_ = crate::leanh::lean_ctor_get(v_m_2275_, 1);
                v_isSharedCheck_2322_ = (!crate::leanh::lean_is_exclusive(v_m_2275_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v___x_2281_ = v_m_2275_;
                    v_isShared_2282_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2279_);
                    crate::leanh::lean_inc(v_size_2278_);
                    crate::leanh::lean_dec(v_m_2275_);
                    v___x_2281_ = crate::leanh::lean_box(0);
                    v_isShared_2282_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2283_ = lean_array_get_size(v_buckets_2279_);
                v___x_2284_ = l_Lean_Syntax_instHashableRange_hash(v_a_2276_);
                v___x_2285_ = 32u64;
                v___x_2286_ = lean_uint64_shift_right(v___x_2284_, v___x_2285_);
                v_fold_2287_ = lean_uint64_xor(v___x_2284_, v___x_2286_);
                v___x_2288_ = 16u64;
                v___x_2289_ = lean_uint64_shift_right(v_fold_2287_, v___x_2288_);
                v___x_2290_ = lean_uint64_xor(v_fold_2287_, v___x_2289_);
                v___x_2291_ = lean_uint64_to_usize(v___x_2290_);
                v___x_2292_ = lean_usize_of_nat(v___x_2283_);
                v___x_2293_ = 1usize;
                v___x_2294_ = lean_usize_sub(v___x_2292_, v___x_2293_);
                v___x_2295_ = lean_usize_land(v___x_2291_, v___x_2294_);
                v_bkt_2296_ = lean_array_uget_borrowed(v_buckets_2279_, v___x_2295_);
                v___x_2297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_2276_, v_bkt_2296_);
                if v___x_2297_ == 0 {
                    v___x_2298_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2299_ = lean_nat_add(v_size_2278_, v___x_2298_);
                    crate::leanh::lean_dec(v_size_2278_);
                    crate::leanh::lean_inc(v_bkt_2296_);
                    v___x_2300_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2300_, 0, v_a_2276_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 1, v_b_2277_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 2, v_bkt_2296_);
                    v_buckets_x27_2301_ =
                        lean_array_uset(v_buckets_2279_, v___x_2295_, v___x_2300_);
                    v___x_2302_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2303_ = lean_nat_mul(v_size_x27_2299_, v___x_2302_);
                    v___x_2304_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2305_ = lean_nat_div(v___x_2303_, v___x_2304_);
                    crate::leanh::lean_dec(v___x_2303_);
                    v___x_2306_ = lean_array_get_size(v_buckets_x27_2301_);
                    v___x_2307_ = lean_nat_dec_le(v___x_2305_, v___x_2306_);
                    crate::leanh::lean_dec(v___x_2305_);
                    if v___x_2307_ == 0 {
                        v_val_2308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_2301_);
                        if v_isShared_2282_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2281_, 1, v_val_2308_);
                            crate::leanh::lean_ctor_set(v___x_2281_, 0, v_size_x27_2299_);
                            v___x_2310_ = v___x_2281_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2311_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2311_,
                                0,
                                v_size_x27_2299_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_val_2308_);
                            v___x_2310_ = v_reuseFailAlloc_2311_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2282_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2281_, 1, v_buckets_x27_2301_);
                            crate::leanh::lean_ctor_set(v___x_2281_, 0, v_size_x27_2299_);
                            v___x_2313_ = v___x_2281_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2314_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2314_,
                                0,
                                v_size_x27_2299_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2314_,
                                1,
                                v_buckets_x27_2301_,
                            );
                            v___x_2313_ = v_reuseFailAlloc_2314_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2296_);
                    v___x_2315_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2316_ =
                        lean_array_uset(v_buckets_2279_, v___x_2295_, v___x_2315_);
                    v___x_2317_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_2276_, v_b_2277_, v_bkt_2296_);
                    v___x_2318_ = lean_array_uset(v_buckets_x27_2316_, v___x_2295_, v___x_2317_);
                    if v_isShared_2282_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2281_, 1, v___x_2318_);
                        v___x_2320_ = v___x_2281_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_size_2278_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2318_);
                        v___x_2320_ = v_reuseFailAlloc_2321_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2310_;
            }
            3 => {
                return v___x_2313_;
            }
            4 => {
                return v___x_2320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(
    mut v_str_2323_: *mut crate::leanh::LeanObject,
    mut v_val_2324_: *mut crate::leanh::LeanObject,
    mut v_info_2325_: *mut crate::leanh::LeanObject,
    mut v___x_2326_: *mut crate::leanh::LeanObject,
    mut v_val_2327_: *mut crate::leanh::LeanObject,
    mut v___x_2328_: u8,
    mut v_as_x27_2329_: *mut crate::leanh::LeanObject,
    mut v_b_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2329_) == 0 {
                    crate::leanh::lean_dec_ref(v_val_2327_);
                    crate::leanh::lean_dec(v___x_2326_);
                    v___x_2333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2333_, 0, v_b_2330_);
                    return v___x_2333_;
                } else {
                    v_head_2334_ = crate::leanh::lean_ctor_get(v_as_x27_2329_, 0);
                    v_tail_2335_ = crate::leanh::lean_ctor_get(v_as_x27_2329_, 1);
                    v___x_2336_ = lean_st_ref_get(v___y_2331_);
                    v_env_2337_ = crate::leanh::lean_ctor_get(v___x_2336_, 0);
                    crate::leanh::lean_inc_ref(v_env_2337_);
                    crate::leanh::lean_dec(v___x_2336_);
                    v___x_2338_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_head_2334_);
                    v___x_2351_ =
                        l_Lean_Environment_find_x3f(v_env_2337_, v_head_2334_, v___x_2328_);
                    if crate::leanh::lean_obj_tag(v___x_2351_) == 1 {
                        v_val_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                        crate::leanh::lean_inc(v_val_2352_);
                        crate::leanh::lean_dec_ref_known(v___x_2351_, 1);
                        if crate::leanh::lean_obj_tag(v_val_2352_) == 6 {
                            v_val_2353_ = crate::leanh::lean_ctor_get(v_val_2352_, 0);
                            crate::leanh::lean_inc_ref(v_val_2353_);
                            crate::leanh::lean_dec_ref_known(v_val_2352_, 1);
                            v_numFields_2354_ = crate::leanh::lean_ctor_get(v_val_2353_, 4);
                            crate::leanh::lean_inc(v_numFields_2354_);
                            crate::leanh::lean_dec_ref(v_val_2353_);
                            v___x_2355_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2356_ = lean_nat_dec_lt(v___x_2355_, v_numFields_2354_);
                            crate::leanh::lean_dec(v_numFields_2354_);
                            if v___x_2356_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v_as_x27_2329_ = v_tail_2335_;
                                v_b_2330_ = v___x_2338_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_2352_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2351_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_head_2334_) == 1 {
                    v_str_2340_ = crate::leanh::lean_ctor_get(v_head_2334_, 1);
                    v___x_2341_ = lean_string_dec_eq(v_str_2340_, v_str_2323_);
                    if v___x_2341_ == 0 {
                        v_as_x27_2329_ = v_tail_2335_;
                        v_b_2330_ = v___x_2338_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2343_ = lean_st_ref_take(v_val_2324_);
                        v___x_2344_ = l_Lean_Elab_Info_stx(v_info_2325_);
                        crate::leanh::lean_inc_ref(v_head_2334_);
                        crate::leanh::lean_inc(v___x_2326_);
                        v___x_2345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2326_);
                        crate::leanh::lean_ctor_set(v___x_2345_, 1, v_head_2334_);
                        v___x_2346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2346_, 0, v___x_2344_);
                        crate::leanh::lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                        crate::leanh::lean_inc_ref(v_val_2327_);
                        v___x_2347_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_2343_, v_val_2327_, v___x_2346_);
                        v___x_2348_ = lean_st_ref_set(v_val_2324_, v___x_2347_);
                        v_as_x27_2329_ = v_tail_2335_;
                        v_b_2330_ = v___x_2338_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_as_x27_2329_ = v_tail_2335_;
                    v_b_2330_ = v___x_2338_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(
    mut v_str_2358_: *mut crate::leanh::LeanObject,
    mut v_val_2359_: *mut crate::leanh::LeanObject,
    mut v_info_2360_: *mut crate::leanh::LeanObject,
    mut v___x_2361_: *mut crate::leanh::LeanObject,
    mut v_val_2362_: *mut crate::leanh::LeanObject,
    mut v___x_2363_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2364_: *mut crate::leanh::LeanObject,
    mut v_b_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_22568__boxed_2368_: u8 = 0;
    let mut v_res_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22568__boxed_2368_ = (crate::leanh::lean_unbox(v___x_2363_) as u8);
    v_res_2369_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(
            v_str_2358_,
            v_val_2359_,
            v_info_2360_,
            v___x_2361_,
            v_val_2362_,
            v___x_22568__boxed_2368_,
            v_as_x27_2364_,
            v_b_2365_,
            v___y_2366_,
        );
    crate::leanh::lean_dec(v___y_2366_);
    crate::leanh::lean_dec(v_as_x27_2364_);
    crate::leanh::lean_dec_ref(v_info_2360_);
    crate::leanh::lean_dec(v_val_2359_);
    crate::leanh::lean_dec_ref(v_str_2358_);
    return v_res_2369_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(
    mut v_ty_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_ty_2370_,
            v___y_2372_,
        );
    if crate::leanh::lean_obj_tag(v___x_2376_) == 0 {
        let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2377_ = crate::leanh::lean_ctor_get(v___x_2376_, 0);
        crate::leanh::lean_inc(v_a_2377_);
        crate::leanh::lean_dec_ref_known(v___x_2376_, 1);
        v___x_2378_ = lean_whnf(
            v_a_2377_,
            v___y_2371_,
            v___y_2372_,
            v___y_2373_,
            v___y_2374_,
        );
        return v___x_2378_;
    } else {
        crate::leanh::lean_dec(v___y_2374_);
        crate::leanh::lean_dec_ref(v___y_2373_);
        crate::leanh::lean_dec(v___y_2372_);
        crate::leanh::lean_dec_ref(v___y_2371_);
        return v___x_2376_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(
    mut v_ty_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
    return v_res_2385_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(
    mut v_val_2386_: *mut crate::leanh::LeanObject,
    mut v___x_2387_: *mut crate::leanh::LeanObject,
    mut v_val_2388_: *mut crate::leanh::LeanObject,
    mut v___x_2389_: *mut crate::leanh::LeanObject,
    mut v_ci_2390_: *mut crate::leanh::LeanObject,
    mut v_info_2391_: *mut crate::leanh::LeanObject,
    mut v_x_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isBinder_2400_: u8 = 0;
    let mut v_fvarId_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v_start_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v_toCommandContextInfo_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_unused_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v_a_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v_ref_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_unused_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2506_: u8 = 0;
    let mut v_a_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v_ref_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2523_: u8 = 0;
    let mut v_isSharedCheck_2524_: u8 = 0;
    let mut v_unused_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_a_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut v_unused_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2573_: u8 = 0;
    let mut v_unused_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_2391_) == 1 {
                    v_i_2396_ = crate::leanh::lean_ctor_get(v_info_2391_, 0);
                    v_expr_2397_ = crate::leanh::lean_ctor_get(v_i_2396_, 3);
                    if crate::leanh::lean_obj_tag(v_expr_2397_) == 1 {
                        v_lctx_2398_ = crate::leanh::lean_ctor_get(v_i_2396_, 1);
                        v_expectedType_x3f_2399_ = crate::leanh::lean_ctor_get(v_i_2396_, 2);
                        v_isBinder_2400_ = crate::leanh::lean_ctor_get_uint8(
                            v_i_2396_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_fvarId_2401_ = crate::leanh::lean_ctor_get(v_expr_2397_, 0);
                        v___x_2402_ = l_Lean_Elab_Info_range_x3f(v_info_2391_);
                        if crate::leanh::lean_obj_tag(v___x_2402_) == 1 {
                            v_val_2403_ = crate::leanh::lean_ctor_get(v___x_2402_, 0);
                            v_isSharedCheck_2558_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2402_)) as u8;
                            if v_isSharedCheck_2558_ == 0 {
                                v___x_2405_ = v___x_2402_;
                                v_isShared_2406_ = v_isSharedCheck_2558_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2403_);
                                crate::leanh::lean_dec(v___x_2402_);
                                v___x_2405_ = crate::leanh::lean_box(0);
                                v_isShared_2406_ = v_isSharedCheck_2558_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2402_);
                            crate::leanh::lean_dec_ref(v_ci_2390_);
                            v_isSharedCheck_2565_ =
                                (!crate::leanh::lean_is_exclusive(v_info_2391_)) as u8;
                            if v_isSharedCheck_2565_ == 0 {
                                v_unused_2566_ = crate::leanh::lean_ctor_get(v_info_2391_, 0);
                                crate::leanh::lean_dec(v_unused_2566_);
                                v___x_2560_ = v_info_2391_;
                                v_isShared_2561_ = v_isSharedCheck_2565_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_info_2391_);
                                v___x_2560_ = crate::leanh::lean_box(0);
                                v_isShared_2561_ = v_isSharedCheck_2565_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ci_2390_);
                        v_isSharedCheck_2573_ =
                            (!crate::leanh::lean_is_exclusive(v_info_2391_)) as u8;
                        if v_isSharedCheck_2573_ == 0 {
                            v_unused_2574_ = crate::leanh::lean_ctor_get(v_info_2391_, 0);
                            crate::leanh::lean_dec(v_unused_2574_);
                            v___x_2568_ = v_info_2391_;
                            v_isShared_2569_ = v_isSharedCheck_2573_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_info_2391_);
                            v___x_2568_ = crate::leanh::lean_box(0);
                            v_isShared_2569_ = v_isSharedCheck_2573_;
                            state = 35;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_2391_);
                    crate::leanh::lean_dec_ref(v_ci_2390_);
                    v___x_2575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2387_);
                    return v___x_2575_;
                }
            }
            1 => {
                v___x_2407_ = lean_st_ref_get(v_val_2386_);
                v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_2407_, v_val_2403_);
                crate::leanh::lean_dec(v___x_2407_);
                if v___x_2408_ == 0 {
                    v___x_2409_ = l_Lean_Elab_Info_stx(v_info_2391_);
                    v___x_2410_ = l_Lean_Syntax_getHeadInfo(v___x_2409_);
                    if crate::leanh::lean_obj_tag(v___x_2410_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2410_, 4);
                        if v_isBinder_2400_ == 0 {
                            crate::leanh::lean_dec(v___x_2409_);
                            crate::leanh::lean_dec(v_val_2403_);
                            crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                            crate::leanh::lean_dec_ref(v_ci_2390_);
                            if v_isShared_2406_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2405_, 0);
                                crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                                v___x_2412_ = v___x_2405_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2413_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2387_);
                                v___x_2412_ = v_reuseFailAlloc_2413_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_fvarId_2401_);
                            crate::leanh::lean_inc_ref(v_lctx_2398_);
                            v___x_2414_ = lean_local_ctx_find(v_lctx_2398_, v_fvarId_2401_);
                            if crate::leanh::lean_obj_tag(v___x_2414_) == 1 {
                                v_val_2415_ = crate::leanh::lean_ctor_get(v___x_2414_, 0);
                                v_isSharedCheck_2548_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2414_)) as u8;
                                if v_isSharedCheck_2548_ == 0 {
                                    v___x_2417_ = v___x_2414_;
                                    v_isShared_2418_ = v_isSharedCheck_2548_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2415_);
                                    crate::leanh::lean_dec(v___x_2414_);
                                    v___x_2417_ = crate::leanh::lean_box(0);
                                    v_isShared_2418_ = v_isSharedCheck_2548_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2414_);
                                crate::leanh::lean_dec(v___x_2409_);
                                crate::leanh::lean_dec(v_val_2403_);
                                crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                                crate::leanh::lean_dec_ref(v_ci_2390_);
                                if v_isShared_2406_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_2405_, 0);
                                    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                                    v___x_2550_ = v___x_2405_;
                                    state = 30;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2551_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2551_,
                                        0,
                                        v___x_2387_,
                                    );
                                    v___x_2550_ = v_reuseFailAlloc_2551_;
                                    state = 30;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2410_);
                        crate::leanh::lean_dec(v___x_2409_);
                        crate::leanh::lean_dec(v_val_2403_);
                        crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                        crate::leanh::lean_dec_ref(v_ci_2390_);
                        if v_isShared_2406_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2405_, 0);
                            crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                            v___x_2553_ = v___x_2405_;
                            state = 31;
                            continue;
                        } else {
                            v_reuseFailAlloc_2554_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2387_);
                            v___x_2553_ = v_reuseFailAlloc_2554_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_2403_);
                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                    crate::leanh::lean_dec_ref(v_ci_2390_);
                    if v_isShared_2406_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2405_, 0);
                        crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                        v___x_2556_ = v___x_2405_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2387_);
                        v___x_2556_ = v_reuseFailAlloc_2557_;
                        state = 32;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2412_;
            }
            3 => {
                v_start_2419_ = crate::leanh::lean_ctor_get(v_val_2403_, 0);
                v___x_2420_ = l_Lean_Syntax_Range_contains(v_val_2388_, v_start_2419_, v___x_2408_);
                if v___x_2420_ == 0 {
                    crate::leanh::lean_dec(v_val_2415_);
                    crate::leanh::lean_dec(v___x_2409_);
                    crate::leanh::lean_del_object(v___x_2405_);
                    crate::leanh::lean_dec(v_val_2403_);
                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                    crate::leanh::lean_dec_ref(v_ci_2390_);
                    if v_isShared_2418_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2417_, 0);
                        crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                        v___x_2422_ = v___x_2417_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2387_);
                        v___x_2422_ = v_reuseFailAlloc_2423_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v___x_2408_ == 0 {
                        v___x_2424_ = l_Lean_LocalDecl_userName(v_val_2415_);
                        crate::leanh::lean_dec(v_val_2415_);
                        v___x_2425_ = l_Lean_Name_hasMacroScopes(v___x_2424_);
                        crate::leanh::lean_dec(v___x_2424_);
                        if v___x_2425_ == 0 {
                            v_toCommandContextInfo_2426_ =
                                crate::leanh::lean_ctor_get(v_ci_2390_, 0);
                            v_options_2427_ =
                                crate::leanh::lean_ctor_get(v_toCommandContextInfo_2426_, 4);
                            crate::leanh::lean_inc_ref(v_options_2427_);
                            v___x_2428_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_2427_, v___y_2394_);
                            if crate::leanh::lean_obj_tag(v___x_2428_) == 0 {
                                v_a_2429_ = crate::leanh::lean_ctor_get(v___x_2428_, 0);
                                v_isSharedCheck_2533_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2428_)) as u8;
                                if v_isSharedCheck_2533_ == 0 {
                                    v___x_2431_ = v___x_2428_;
                                    v_isShared_2432_ = v_isSharedCheck_2533_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2429_);
                                    crate::leanh::lean_dec(v___x_2428_);
                                    v___x_2431_ = crate::leanh::lean_box(0);
                                    v_isShared_2432_ = v_isSharedCheck_2533_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2417_);
                                crate::leanh::lean_dec(v___x_2409_);
                                crate::leanh::lean_del_object(v___x_2405_);
                                crate::leanh::lean_dec(v_val_2403_);
                                crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                                crate::leanh::lean_dec_ref(v_ci_2390_);
                                v_a_2534_ = crate::leanh::lean_ctor_get(v___x_2428_, 0);
                                v_isSharedCheck_2541_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2428_)) as u8;
                                if v_isSharedCheck_2541_ == 0 {
                                    v___x_2536_ = v___x_2428_;
                                    v_isShared_2537_ = v_isSharedCheck_2541_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2534_);
                                    crate::leanh::lean_dec(v___x_2428_);
                                    v___x_2536_ = crate::leanh::lean_box(0);
                                    v_isShared_2537_ = v_isSharedCheck_2541_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2409_);
                            crate::leanh::lean_del_object(v___x_2405_);
                            crate::leanh::lean_dec(v_val_2403_);
                            crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                            crate::leanh::lean_dec_ref(v_ci_2390_);
                            if v_isShared_2418_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2417_, 0);
                                crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                                v___x_2543_ = v___x_2417_;
                                state = 28;
                                continue;
                            } else {
                                v_reuseFailAlloc_2544_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2387_);
                                v___x_2543_ = v_reuseFailAlloc_2544_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2415_);
                        crate::leanh::lean_dec(v___x_2409_);
                        crate::leanh::lean_del_object(v___x_2405_);
                        crate::leanh::lean_dec(v_val_2403_);
                        crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                        crate::leanh::lean_dec_ref(v_ci_2390_);
                        if v_isShared_2418_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2417_, 0);
                            crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                            v___x_2546_ = v___x_2417_;
                            state = 29;
                            continue;
                        } else {
                            v_reuseFailAlloc_2547_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2387_);
                            v___x_2546_ = v_reuseFailAlloc_2547_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2422_;
            }
            5 => {
                v___x_2433_ = l_Lean_Linter_getLinterValue(v___x_2389_, v_a_2429_);
                crate::leanh::lean_dec(v_a_2429_);
                if v___x_2433_ == 0 {
                    crate::leanh::lean_del_object(v___x_2417_);
                    crate::leanh::lean_dec(v___x_2409_);
                    crate::leanh::lean_del_object(v___x_2405_);
                    crate::leanh::lean_dec(v_val_2403_);
                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                    crate::leanh::lean_dec_ref(v_ci_2390_);
                    if v_isShared_2432_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                        v___x_2435_ = v___x_2431_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2387_);
                        v___x_2435_ = v_reuseFailAlloc_2436_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2437_ = l_Lean_Syntax_getId(v___x_2409_);
                    crate::leanh::lean_dec(v___x_2409_);
                    if crate::leanh::lean_obj_tag(v___x_2437_) == 1 {
                        v_pre_2438_ = crate::leanh::lean_ctor_get(v___x_2437_, 0);
                        crate::leanh::lean_inc(v_pre_2438_);
                        v_str_2439_ = crate::leanh::lean_ctor_get(v___x_2437_, 1);
                        crate::leanh::lean_inc_ref(v_str_2439_);
                        if crate::leanh::lean_obj_tag(v_pre_2438_) == 0 {
                            crate::leanh::lean_del_object(v___x_2431_);
                            if crate::leanh::lean_obj_tag(v_expectedType_x3f_2399_) == 1 {
                                crate::leanh::lean_del_object(v___x_2405_);
                                v_val_2500_ =
                                    crate::leanh::lean_ctor_get(v_expectedType_x3f_2399_, 0);
                                crate::leanh::lean_inc(v_val_2500_);
                                v_ty_2441_ = v_val_2500_;
                                v___y_2442_ = v___y_2393_;
                                v___y_2443_ = v___y_2394_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_expr_2397_);
                                v___x_2501_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                                    6,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___x_2501_, 0, v_expr_2397_);
                                crate::leanh::lean_inc_ref(v_ci_2390_);
                                crate::leanh::lean_inc_ref(v_i_2396_);
                                v___x_2502_ = l_Lean_Elab_TermInfo_runMetaM___redArg(
                                    v_i_2396_,
                                    v_ci_2390_,
                                    v___x_2501_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2502_) == 0 {
                                    crate::leanh::lean_del_object(v___x_2405_);
                                    v_a_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                                    crate::leanh::lean_inc(v_a_2503_);
                                    crate::leanh::lean_dec_ref_known(v___x_2502_, 1);
                                    v_ty_2441_ = v_a_2503_;
                                    v___y_2442_ = v___y_2393_;
                                    v___y_2443_ = v___y_2394_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_str_2439_);
                                    crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                                    crate::leanh::lean_del_object(v___x_2417_);
                                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                                    crate::leanh::lean_dec_ref(v_ci_2390_);
                                    v_isSharedCheck_2524_ =
                                        (!crate::leanh::lean_is_exclusive(v_val_2403_)) as u8;
                                    if v_isSharedCheck_2524_ == 0 {
                                        v_unused_2525_ =
                                            crate::leanh::lean_ctor_get(v_val_2403_, 1);
                                        crate::leanh::lean_dec(v_unused_2525_);
                                        v_unused_2526_ =
                                            crate::leanh::lean_ctor_get(v_val_2403_, 0);
                                        crate::leanh::lean_dec(v_unused_2526_);
                                        v___x_2505_ = v_val_2403_;
                                        v_isShared_2506_ = v_isSharedCheck_2524_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_val_2403_);
                                        v___x_2505_ = crate::leanh::lean_box(0);
                                        v_isShared_2506_ = v_isSharedCheck_2524_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_str_2439_);
                            crate::leanh::lean_dec(v_pre_2438_);
                            crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                            crate::leanh::lean_del_object(v___x_2417_);
                            crate::leanh::lean_del_object(v___x_2405_);
                            crate::leanh::lean_dec(v_val_2403_);
                            crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                            crate::leanh::lean_dec_ref(v_ci_2390_);
                            if v_isShared_2432_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                                v___x_2528_ = v___x_2431_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_2529_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2387_);
                                v___x_2528_ = v_reuseFailAlloc_2529_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2437_);
                        crate::leanh::lean_del_object(v___x_2417_);
                        crate::leanh::lean_del_object(v___x_2405_);
                        crate::leanh::lean_dec(v_val_2403_);
                        crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                        crate::leanh::lean_dec_ref(v_ci_2390_);
                        if v_isShared_2432_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                            v___x_2531_ = v___x_2431_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_2532_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2387_);
                            v___x_2531_ = v_reuseFailAlloc_2532_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_2435_;
            }
            7 => {
                v___f_2444_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed as *mut core::ffi::c_void, 6, 1);
                crate::leanh::lean_closure_set(v___f_2444_, 0, v_ty_2441_);
                crate::leanh::lean_inc_ref(v_i_2396_);
                v___x_2445_ =
                    l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_2396_, v_ci_2390_, v___f_2444_);
                if crate::leanh::lean_obj_tag(v___x_2445_) == 0 {
                    crate::leanh::lean_del_object(v___x_2417_);
                    v_a_2446_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2476_ = (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2448_ = v___x_2445_;
                        v_isShared_2449_ = v_isSharedCheck_2476_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2446_);
                        crate::leanh::lean_dec(v___x_2445_);
                        v___x_2448_ = crate::leanh::lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2476_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_str_2439_);
                    crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                    v_isSharedCheck_2497_ = (!crate::leanh::lean_is_exclusive(v_val_2403_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v_unused_2498_ = crate::leanh::lean_ctor_get(v_val_2403_, 1);
                        crate::leanh::lean_dec(v_unused_2498_);
                        v_unused_2499_ = crate::leanh::lean_ctor_get(v_val_2403_, 0);
                        crate::leanh::lean_dec(v_unused_2499_);
                        v___x_2478_ = v_val_2403_;
                        v_isShared_2479_ = v_isSharedCheck_2497_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_2403_);
                        v___x_2478_ = crate::leanh::lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2497_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2450_ = l_Lean_Expr_getAppFn_x27(v_a_2446_);
                crate::leanh::lean_dec(v_a_2446_);
                if crate::leanh::lean_obj_tag(v___x_2450_) == 4 {
                    v_declName_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                    crate::leanh::lean_inc(v_declName_2451_);
                    crate::leanh::lean_dec_ref_known(v___x_2450_, 2);
                    v___x_2452_ = lean_st_ref_get(v___y_2443_);
                    v_env_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                    crate::leanh::lean_inc_ref(v_env_2453_);
                    crate::leanh::lean_dec(v___x_2452_);
                    v___x_2454_ =
                        l_Lean_Environment_find_x3f(v_env_2453_, v_declName_2451_, v___x_2408_);
                    if crate::leanh::lean_obj_tag(v___x_2454_) == 1 {
                        v_val_2455_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                        crate::leanh::lean_inc(v_val_2455_);
                        crate::leanh::lean_dec_ref_known(v___x_2454_, 1);
                        if crate::leanh::lean_obj_tag(v_val_2455_) == 5 {
                            crate::leanh::lean_del_object(v___x_2448_);
                            v_val_2456_ = crate::leanh::lean_ctor_get(v_val_2455_, 0);
                            crate::leanh::lean_inc_ref(v_val_2456_);
                            crate::leanh::lean_dec_ref_known(v_val_2455_, 1);
                            v_ctors_2457_ = crate::leanh::lean_ctor_get(v_val_2456_, 4);
                            crate::leanh::lean_inc(v_ctors_2457_);
                            crate::leanh::lean_dec_ref(v_val_2456_);
                            v___x_2458_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_2439_, v_val_2386_, v_info_2391_, v___x_2437_, v_val_2403_, v___x_2408_, v_ctors_2457_, v___x_2387_, v___y_2443_);
                            crate::leanh::lean_dec(v_ctors_2457_);
                            crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                            crate::leanh::lean_dec_ref(v_str_2439_);
                            if crate::leanh::lean_obj_tag(v___x_2458_) == 0 {
                                v_isSharedCheck_2465_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2458_)) as u8;
                                if v_isSharedCheck_2465_ == 0 {
                                    v_unused_2466_ = crate::leanh::lean_ctor_get(v___x_2458_, 0);
                                    crate::leanh::lean_dec(v_unused_2466_);
                                    v___x_2460_ = v___x_2458_;
                                    v_isShared_2461_ = v_isSharedCheck_2465_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2458_);
                                    v___x_2460_ = crate::leanh::lean_box(0);
                                    v_isShared_2461_ = v_isSharedCheck_2465_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                return v___x_2458_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_2455_);
                            crate::leanh::lean_dec_ref(v_str_2439_);
                            crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                            crate::leanh::lean_dec(v_val_2403_);
                            crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                            if v_isShared_2449_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                                v___x_2468_ = v___x_2448_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2469_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2387_);
                                v___x_2468_ = v_reuseFailAlloc_2469_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2454_);
                        crate::leanh::lean_dec_ref(v_str_2439_);
                        crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                        crate::leanh::lean_dec(v_val_2403_);
                        crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                        if v_isShared_2449_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                            v___x_2471_ = v___x_2448_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2472_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2387_);
                            v___x_2471_ = v_reuseFailAlloc_2472_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2450_);
                    crate::leanh::lean_dec_ref(v_str_2439_);
                    crate::leanh::lean_dec_ref_known(v___x_2437_, 2);
                    crate::leanh::lean_dec(v_val_2403_);
                    crate::leanh::lean_dec_ref_known(v_info_2391_, 1);
                    if v_isShared_2449_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                        v___x_2474_ = v___x_2448_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2387_);
                        v___x_2474_ = v_reuseFailAlloc_2475_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2460_, 0, v___x_2387_);
                    v___x_2463_ = v___x_2460_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2387_);
                    v___x_2463_ = v_reuseFailAlloc_2464_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2463_;
            }
            11 => {
                return v___x_2468_;
            }
            12 => {
                return v___x_2471_;
            }
            13 => {
                return v___x_2474_;
            }
            14 => {
                v_a_2480_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                v_isSharedCheck_2496_ = (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                if v_isSharedCheck_2496_ == 0 {
                    v___x_2482_ = v___x_2445_;
                    v_isShared_2483_ = v_isSharedCheck_2496_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2480_);
                    crate::leanh::lean_dec(v___x_2445_);
                    v___x_2482_ = crate::leanh::lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2496_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_ref_2484_ = crate::leanh::lean_ctor_get(v___y_2442_, 7);
                v___x_2485_ = lean_io_error_to_string(v_a_2480_);
                if v_isShared_2418_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2417_, 3);
                    crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2485_);
                    v___x_2487_ = v___x_2417_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2485_);
                    v___x_2487_ = v_reuseFailAlloc_2495_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2488_ = l_Lean_MessageData_ofFormat(v___x_2487_);
                crate::leanh::lean_inc(v_ref_2484_);
                if v_isShared_2479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2478_, 1, v___x_2488_);
                    crate::leanh::lean_ctor_set(v___x_2478_, 0, v_ref_2484_);
                    v___x_2490_ = v___x_2478_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_ref_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2488_);
                    v___x_2490_ = v_reuseFailAlloc_2494_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2490_);
                    v___x_2492_ = v___x_2482_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                    v___x_2492_ = v_reuseFailAlloc_2493_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2492_;
            }
            19 => {
                v_a_2507_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                v_isSharedCheck_2523_ = (!crate::leanh::lean_is_exclusive(v___x_2502_)) as u8;
                if v_isSharedCheck_2523_ == 0 {
                    v___x_2509_ = v___x_2502_;
                    v_isShared_2510_ = v_isSharedCheck_2523_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2507_);
                    crate::leanh::lean_dec(v___x_2502_);
                    v___x_2509_ = crate::leanh::lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2523_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_ref_2511_ = crate::leanh::lean_ctor_get(v___y_2393_, 7);
                v___x_2512_ = lean_io_error_to_string(v_a_2507_);
                if v_isShared_2406_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2405_, 3);
                    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2512_);
                    v___x_2514_ = v___x_2405_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2522_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
                    v___x_2514_ = v_reuseFailAlloc_2522_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2515_ = l_Lean_MessageData_ofFormat(v___x_2514_);
                crate::leanh::lean_inc(v_ref_2511_);
                if v_isShared_2506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2505_, 1, v___x_2515_);
                    crate::leanh::lean_ctor_set(v___x_2505_, 0, v_ref_2511_);
                    v___x_2517_ = v___x_2505_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_ref_2511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2515_);
                    v___x_2517_ = v_reuseFailAlloc_2521_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2509_, 0, v___x_2517_);
                    v___x_2519_ = v___x_2509_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
                    v___x_2519_ = v_reuseFailAlloc_2520_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2519_;
            }
            24 => {
                return v___x_2528_;
            }
            25 => {
                return v___x_2531_;
            }
            26 => {
                if v_isShared_2537_ == 0 {
                    v___x_2539_ = v___x_2536_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2539_;
            }
            28 => {
                return v___x_2543_;
            }
            29 => {
                return v___x_2546_;
            }
            30 => {
                return v___x_2550_;
            }
            31 => {
                return v___x_2553_;
            }
            32 => {
                return v___x_2556_;
            }
            33 => {
                if v_isShared_2561_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2560_, 0);
                    crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2387_);
                    v___x_2563_ = v___x_2560_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2387_);
                    v___x_2563_ = v_reuseFailAlloc_2564_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2563_;
            }
            35 => {
                if v_isShared_2569_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2568_, 0);
                    crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2387_);
                    v___x_2571_ = v___x_2568_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2387_);
                    v___x_2571_ = v_reuseFailAlloc_2572_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(
    mut v_val_2576_: *mut crate::leanh::LeanObject,
    mut v___x_2577_: *mut crate::leanh::LeanObject,
    mut v_val_2578_: *mut crate::leanh::LeanObject,
    mut v___x_2579_: *mut crate::leanh::LeanObject,
    mut v_ci_2580_: *mut crate::leanh::LeanObject,
    mut v_info_2581_: *mut crate::leanh::LeanObject,
    mut v_x_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_2576_, v___x_2577_, v_val_2578_, v___x_2579_, v_ci_2580_, v_info_2581_, v_x_2582_, v___y_2583_, v___y_2584_);
    crate::leanh::lean_dec(v___y_2584_);
    crate::leanh::lean_dec_ref(v___y_2583_);
    crate::leanh::lean_dec_ref(v_x_2582_);
    crate::leanh::lean_dec_ref(v___x_2579_);
    crate::leanh::lean_dec_ref(v_val_2578_);
    crate::leanh::lean_dec(v_val_2576_);
    return v_res_2586_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(
    mut v_postNode_2587_: *mut crate::leanh::LeanObject,
    mut v_ci_2588_: *mut crate::leanh::LeanObject,
    mut v_i_2589_: *mut crate::leanh::LeanObject,
    mut v_cs_2590_: *mut crate::leanh::LeanObject,
    mut v_x_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2593_);
    crate::leanh::lean_inc_ref(v___y_2592_);
    v___x_2595_ = crate::leanh::lean_apply_6(
        v_postNode_2587_,
        v_ci_2588_,
        v_i_2589_,
        v_cs_2590_,
        v___y_2592_,
        v___y_2593_,
        crate::leanh::lean_box(0),
    );
    return v___x_2595_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(
    mut v_postNode_2596_: *mut crate::leanh::LeanObject,
    mut v_ci_2597_: *mut crate::leanh::LeanObject,
    mut v_i_2598_: *mut crate::leanh::LeanObject,
    mut v_cs_2599_: *mut crate::leanh::LeanObject,
    mut v_x_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_2596_, v_ci_2597_, v_i_2598_, v_cs_2599_, v_x_2600_, v___y_2601_, v___y_2602_);
    crate::leanh::lean_dec(v___y_2602_);
    crate::leanh::lean_dec_ref(v___y_2601_);
    crate::leanh::lean_dec(v_x_2600_);
    return v_res_2604_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2605_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(
    mut v_msg_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v_toFunctor_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___f_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18811__overap_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_unused_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_unused_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
                v___x_2613_ = l_StateRefT_x27_instMonad___redArg(v___x_2612_);
                v_toApplicative_2614_ = crate::leanh::lean_ctor_get(v___x_2613_, 0);
                v_isSharedCheck_2645_ = (!crate::leanh::lean_is_exclusive(v___x_2613_)) as u8;
                if v_isSharedCheck_2645_ == 0 {
                    v_unused_2646_ = crate::leanh::lean_ctor_get(v___x_2613_, 1);
                    crate::leanh::lean_dec(v_unused_2646_);
                    v___x_2616_ = v___x_2613_;
                    v_isShared_2617_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2614_);
                    crate::leanh::lean_dec(v___x_2613_);
                    v___x_2616_ = crate::leanh::lean_box(0);
                    v_isShared_2617_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2618_ = crate::leanh::lean_ctor_get(v_toApplicative_2614_, 0);
                v_toSeq_2619_ = crate::leanh::lean_ctor_get(v_toApplicative_2614_, 2);
                v_toSeqLeft_2620_ = crate::leanh::lean_ctor_get(v_toApplicative_2614_, 3);
                v_toSeqRight_2621_ = crate::leanh::lean_ctor_get(v_toApplicative_2614_, 4);
                v_isSharedCheck_2643_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2614_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v_unused_2644_ = crate::leanh::lean_ctor_get(v_toApplicative_2614_, 1);
                    crate::leanh::lean_dec(v_unused_2644_);
                    v___x_2623_ = v_toApplicative_2614_;
                    v_isShared_2624_ = v_isSharedCheck_2643_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2621_);
                    crate::leanh::lean_inc(v_toSeqLeft_2620_);
                    crate::leanh::lean_inc(v_toSeq_2619_);
                    crate::leanh::lean_inc(v_toFunctor_2618_);
                    crate::leanh::lean_dec(v_toApplicative_2614_);
                    v___x_2623_ = crate::leanh::lean_box(0);
                    v_isShared_2624_ = v_isSharedCheck_2643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2625_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1;
                v___f_2626_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2618_);
                v___f_2627_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2627_, 0, v_toFunctor_2618_);
                v___f_2628_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2628_, 0, v_toFunctor_2618_);
                v___x_2629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2629_, 0, v___f_2627_);
                crate::leanh::lean_ctor_set(v___x_2629_, 1, v___f_2628_);
                v___f_2630_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2630_, 0, v_toSeqRight_2621_);
                v___f_2631_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2631_, 0, v_toSeqLeft_2620_);
                v___f_2632_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2632_, 0, v_toSeq_2619_);
                if v_isShared_2624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2623_, 4, v___f_2630_);
                    crate::leanh::lean_ctor_set(v___x_2623_, 3, v___f_2631_);
                    crate::leanh::lean_ctor_set(v___x_2623_, 2, v___f_2632_);
                    crate::leanh::lean_ctor_set(v___x_2623_, 1, v___f_2625_);
                    crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2629_);
                    v___x_2634_ = v___x_2623_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___f_2625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 2, v___f_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 3, v___f_2631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___f_2630_);
                    v___x_2634_ = v_reuseFailAlloc_2642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2616_, 1, v___f_2626_);
                    crate::leanh::lean_ctor_set(v___x_2616_, 0, v___x_2634_);
                    v___x_2636_ = v___x_2616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___f_2626_);
                    v___x_2636_ = v_reuseFailAlloc_2641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2637_ = crate::leanh::lean_box(0);
                v___x_2638_ = l_instInhabitedOfMonad___redArg(v___x_2636_, v___x_2637_);
                v___x_18811__overap_2639_ = lean_panic_fn_borrowed(v___x_2638_, v_msg_2608_);
                crate::leanh::lean_dec(v___x_2638_);
                crate::leanh::lean_inc(v___y_2610_);
                crate::leanh::lean_inc_ref(v___y_2609_);
                v___x_2640_ = crate::leanh::lean_apply_3(
                    v___x_18811__overap_2639_,
                    v___y_2609_,
                    v___y_2610_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(
    mut v_msg_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_2647_, v___y_2648_, v___y_2649_);
    crate::leanh::lean_dec(v___y_2649_);
    crate::leanh::lean_dec_ref(v___y_2648_);
    return v_res_2651_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2;
    v___x_2656_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2657_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_2658_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1;
    v___x_2659_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0;
    v___x_2660_ = l_mkPanicMessageWithDecl(
        v___x_2659_,
        v___x_2658_,
        v___x_2657_,
        v___x_2656_,
        v___x_2655_,
    );
    return v___x_2660_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(
    mut v_preNode_2661_: *mut crate::leanh::LeanObject,
    mut v_postNode_2662_: *mut crate::leanh::LeanObject,
    mut v_x_2663_: *mut crate::leanh::LeanObject,
    mut v_x_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_a_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_unused_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_a_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_a_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2740_: u8 = 0;
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut v_unused_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2664_) {
                0 => {
                    v_i_2668_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                    crate::leanh::lean_inc_ref(v_i_2668_);
                    v_t_2669_ = crate::leanh::lean_ctor_get(v_x_2664_, 1);
                    crate::leanh::lean_inc_ref(v_t_2669_);
                    crate::leanh::lean_dec_ref_known(v_x_2664_, 2);
                    v___x_2670_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2668_, v_x_2663_);
                    v_x_2663_ = v___x_2670_;
                    v_x_2664_ = v_t_2669_;
                    state = 0;
                    continue;
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_2663_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_2664_, 2);
                        crate::leanh::lean_dec_ref(v_postNode_2662_);
                        crate::leanh::lean_dec_ref(v_preNode_2661_);
                        v___x_2672_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
                        v___x_2673_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_2672_, v___y_2665_, v___y_2666_);
                        return v___x_2673_;
                    } else {
                        v_i_2674_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                        crate::leanh::lean_inc_ref_n(v_i_2674_, 2);
                        v_children_2675_ = crate::leanh::lean_ctor_get(v_x_2664_, 1);
                        crate::leanh::lean_inc_ref_n(v_children_2675_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_2664_, 2);
                        v_val_2676_ = crate::leanh::lean_ctor_get(v_x_2663_, 0);
                        crate::leanh::lean_inc_n(v_val_2676_, 2);
                        crate::leanh::lean_inc_ref(v_preNode_2661_);
                        crate::leanh::lean_inc(v___y_2666_);
                        crate::leanh::lean_inc_ref(v___y_2665_);
                        v___x_2677_ = crate::leanh::lean_apply_6(
                            v_preNode_2661_,
                            v_val_2676_,
                            v_i_2674_,
                            v_children_2675_,
                            v___y_2665_,
                            v___y_2666_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_2677_) == 0 {
                            v_a_2678_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                            crate::leanh::lean_inc(v_a_2678_);
                            crate::leanh::lean_dec_ref_known(v___x_2677_, 1);
                            v___x_2679_ = (crate::leanh::lean_unbox(v_a_2678_) as u8);
                            crate::leanh::lean_dec(v_a_2678_);
                            if v___x_2679_ == 0 {
                                crate::leanh::lean_dec_ref(v_preNode_2661_);
                                v_isSharedCheck_2704_ =
                                    (!crate::leanh::lean_is_exclusive(v_x_2663_)) as u8;
                                if v_isSharedCheck_2704_ == 0 {
                                    v_unused_2705_ = crate::leanh::lean_ctor_get(v_x_2663_, 0);
                                    crate::leanh::lean_dec(v_unused_2705_);
                                    v___x_2681_ = v_x_2663_;
                                    v_isShared_2682_ = v_isSharedCheck_2704_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_x_2663_);
                                    v___x_2681_ = crate::leanh::lean_box(0);
                                    v_isShared_2682_ = v_isSharedCheck_2704_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2706_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_2663_, v_i_2674_);
                                v___x_2707_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_2675_);
                                v___x_2708_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_ref(v_postNode_2662_);
                                v___x_2709_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_2661_, v_postNode_2662_, v___x_2706_, v___x_2707_, v___x_2708_, v___y_2665_, v___y_2666_);
                                if crate::leanh::lean_obj_tag(v___x_2709_) == 0 {
                                    v_a_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                                    crate::leanh::lean_inc(v_a_2710_);
                                    crate::leanh::lean_dec_ref_known(v___x_2709_, 1);
                                    crate::leanh::lean_inc(v___y_2666_);
                                    crate::leanh::lean_inc_ref(v___y_2665_);
                                    v___x_2711_ = crate::leanh::lean_apply_7(
                                        v_postNode_2662_,
                                        v_val_2676_,
                                        v_i_2674_,
                                        v_children_2675_,
                                        v_a_2710_,
                                        v___y_2665_,
                                        v___y_2666_,
                                        crate::leanh::lean_box(0),
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2711_) == 0 {
                                        v_a_2712_ = crate::leanh::lean_ctor_get(v___x_2711_, 0);
                                        v_isSharedCheck_2720_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2711_)) as u8;
                                        if v_isSharedCheck_2720_ == 0 {
                                            v___x_2714_ = v___x_2711_;
                                            v_isShared_2715_ = v_isSharedCheck_2720_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2712_);
                                            crate::leanh::lean_dec(v___x_2711_);
                                            v___x_2714_ = crate::leanh::lean_box(0);
                                            v_isShared_2715_ = v_isSharedCheck_2720_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2711_, 0);
                                        v_isSharedCheck_2728_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2711_)) as u8;
                                        if v_isSharedCheck_2728_ == 0 {
                                            v___x_2723_ = v___x_2711_;
                                            v_isShared_2724_ = v_isSharedCheck_2728_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2721_);
                                            crate::leanh::lean_dec(v___x_2711_);
                                            v___x_2723_ = crate::leanh::lean_box(0);
                                            v_isShared_2724_ = v_isSharedCheck_2728_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_2676_);
                                    crate::leanh::lean_dec_ref(v_children_2675_);
                                    crate::leanh::lean_dec_ref(v_i_2674_);
                                    crate::leanh::lean_dec_ref(v_postNode_2662_);
                                    v_a_2729_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                                    v_isSharedCheck_2736_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                                    if v_isSharedCheck_2736_ == 0 {
                                        v___x_2731_ = v___x_2709_;
                                        v_isShared_2732_ = v_isSharedCheck_2736_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2729_);
                                        crate::leanh::lean_dec(v___x_2709_);
                                        v___x_2731_ = crate::leanh::lean_box(0);
                                        v_isShared_2732_ = v_isSharedCheck_2736_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_2676_);
                            crate::leanh::lean_dec_ref(v_children_2675_);
                            crate::leanh::lean_dec_ref_known(v_x_2663_, 1);
                            crate::leanh::lean_dec_ref(v_i_2674_);
                            crate::leanh::lean_dec_ref(v_postNode_2662_);
                            crate::leanh::lean_dec_ref(v_preNode_2661_);
                            v_a_2737_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                            v_isSharedCheck_2744_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2677_)) as u8;
                            if v_isSharedCheck_2744_ == 0 {
                                v___x_2739_ = v___x_2677_;
                                v_isShared_2740_ = v_isSharedCheck_2744_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2737_);
                                crate::leanh::lean_dec(v___x_2677_);
                                v___x_2739_ = crate::leanh::lean_box(0);
                                v_isShared_2740_ = v_isSharedCheck_2744_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_2663_);
                    crate::leanh::lean_dec_ref(v_postNode_2662_);
                    crate::leanh::lean_dec_ref(v_preNode_2661_);
                    v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v_unused_2753_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                        crate::leanh::lean_dec(v_unused_2753_);
                        v___x_2746_ = v_x_2664_;
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2664_);
                        v___x_2746_ = crate::leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2683_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2666_);
                crate::leanh::lean_inc_ref(v___y_2665_);
                v___x_2684_ = crate::leanh::lean_apply_7(
                    v_postNode_2662_,
                    v_val_2676_,
                    v_i_2674_,
                    v_children_2675_,
                    v___x_2683_,
                    v___y_2665_,
                    v___y_2666_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2684_) == 0 {
                    v_a_2685_ = crate::leanh::lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2695_ = (!crate::leanh::lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2695_ == 0 {
                        v___x_2687_ = v___x_2684_;
                        v_isShared_2688_ = v_isSharedCheck_2695_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2685_);
                        crate::leanh::lean_dec(v___x_2684_);
                        v___x_2687_ = crate::leanh::lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2695_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2681_);
                    v_a_2696_ = crate::leanh::lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2703_ = (!crate::leanh::lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2698_ = v___x_2684_;
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2696_);
                        crate::leanh::lean_dec(v___x_2684_);
                        v___x_2698_ = crate::leanh::lean_box(0);
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2681_, 0, v_a_2685_);
                    v___x_2690_ = v___x_2681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2685_);
                    v___x_2690_ = v_reuseFailAlloc_2694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2690_);
                    v___x_2692_ = v___x_2687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
                    v___x_2692_ = v_reuseFailAlloc_2693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2692_;
            }
            5 => {
                if v_isShared_2699_ == 0 {
                    v___x_2701_ = v___x_2698_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2701_;
            }
            7 => {
                v___x_2716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2716_, 0, v_a_2712_);
                if v_isShared_2715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2714_, 0, v___x_2716_);
                    v___x_2718_ = v___x_2714_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                    v___x_2718_ = v_reuseFailAlloc_2719_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2718_;
            }
            9 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2726_;
            }
            11 => {
                if v_isShared_2732_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
                    v___x_2734_ = v_reuseFailAlloc_2735_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2734_;
            }
            13 => {
                if v_isShared_2740_ == 0 {
                    v___x_2742_ = v___x_2739_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
                    v___x_2742_ = v_reuseFailAlloc_2743_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2742_;
            }
            15 => {
                v___x_2748_ = crate::leanh::lean_box(0);
                if v_isShared_2747_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2746_, 0);
                    crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2746_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
                    v___x_2750_ = v_reuseFailAlloc_2751_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(
    mut v_preNode_2754_: *mut crate::leanh::LeanObject,
    mut v_postNode_2755_: *mut crate::leanh::LeanObject,
    mut v___x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v_x_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2757_) == 0 {
                    crate::leanh::lean_dec(v___x_2756_);
                    crate::leanh::lean_dec_ref(v_postNode_2755_);
                    crate::leanh::lean_dec_ref(v_preNode_2754_);
                    v___x_2762_ = l_List_reverse___redArg(v_x_2758_);
                    v___x_2763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2763_, 0, v___x_2762_);
                    return v___x_2763_;
                } else {
                    v_head_2764_ = crate::leanh::lean_ctor_get(v_x_2757_, 0);
                    v_tail_2765_ = crate::leanh::lean_ctor_get(v_x_2757_, 1);
                    v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v_x_2757_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2767_ = v_x_2757_;
                        v_isShared_2768_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2765_);
                        crate::leanh::lean_inc(v_head_2764_);
                        crate::leanh::lean_dec(v_x_2757_);
                        v___x_2767_ = crate::leanh::lean_box(0);
                        v_isShared_2768_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_2756_);
                crate::leanh::lean_inc_ref(v_postNode_2755_);
                crate::leanh::lean_inc_ref(v_preNode_2754_);
                v___x_2769_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2754_, v_postNode_2755_, v___x_2756_, v_head_2764_, v___y_2759_, v___y_2760_);
                if crate::leanh::lean_obj_tag(v___x_2769_) == 0 {
                    v_a_2770_ = crate::leanh::lean_ctor_get(v___x_2769_, 0);
                    crate::leanh::lean_inc(v_a_2770_);
                    crate::leanh::lean_dec_ref_known(v___x_2769_, 1);
                    if v_isShared_2768_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2767_, 1, v_x_2758_);
                        crate::leanh::lean_ctor_set(v___x_2767_, 0, v_a_2770_);
                        v___x_2772_ = v___x_2767_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2770_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_x_2758_);
                        v___x_2772_ = v_reuseFailAlloc_2774_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2767_);
                    crate::leanh::lean_dec(v_tail_2765_);
                    crate::leanh::lean_dec(v_x_2758_);
                    crate::leanh::lean_dec(v___x_2756_);
                    crate::leanh::lean_dec_ref(v_postNode_2755_);
                    crate::leanh::lean_dec_ref(v_preNode_2754_);
                    v_a_2775_ = crate::leanh::lean_ctor_get(v___x_2769_, 0);
                    v_isSharedCheck_2782_ = (!crate::leanh::lean_is_exclusive(v___x_2769_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v___x_2777_ = v___x_2769_;
                        v_isShared_2778_ = v_isSharedCheck_2782_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2775_);
                        crate::leanh::lean_dec(v___x_2769_);
                        v___x_2777_ = crate::leanh::lean_box(0);
                        v_isShared_2778_ = v_isSharedCheck_2782_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_2757_ = v_tail_2765_;
                v_x_2758_ = v___x_2772_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2778_ == 0 {
                    v___x_2780_ = v___x_2777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
                    v___x_2780_ = v_reuseFailAlloc_2781_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(
    mut v_preNode_2784_: *mut crate::leanh::LeanObject,
    mut v_postNode_2785_: *mut crate::leanh::LeanObject,
    mut v___x_2786_: *mut crate::leanh::LeanObject,
    mut v_x_2787_: *mut crate::leanh::LeanObject,
    mut v_x_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_2784_, v_postNode_2785_, v___x_2786_, v_x_2787_, v_x_2788_, v___y_2789_, v___y_2790_);
    crate::leanh::lean_dec(v___y_2790_);
    crate::leanh::lean_dec_ref(v___y_2789_);
    return v_res_2792_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(
    mut v_preNode_2793_: *mut crate::leanh::LeanObject,
    mut v_postNode_2794_: *mut crate::leanh::LeanObject,
    mut v_x_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
    mut v___y_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2793_, v_postNode_2794_, v_x_2795_, v_x_2796_, v___y_2797_, v___y_2798_);
    crate::leanh::lean_dec(v___y_2798_);
    crate::leanh::lean_dec_ref(v___y_2797_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(
    mut v_preNode_2801_: *mut crate::leanh::LeanObject,
    mut v_postNode_2802_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2803_: *mut crate::leanh::LeanObject,
    mut v_t_2804_: *mut crate::leanh::LeanObject,
    mut v___y_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_unused_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2808_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2808_, 0, v_postNode_2802_);
                v___x_2809_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2801_, v___f_2808_, v_ctx_x3f_2803_, v_t_2804_, v___y_2805_, v___y_2806_);
                if crate::leanh::lean_obj_tag(v___x_2809_) == 0 {
                    v_isSharedCheck_2817_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v_unused_2818_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                        crate::leanh::lean_dec(v_unused_2818_);
                        v___x_2811_ = v___x_2809_;
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2809_);
                        v___x_2811_ = crate::leanh::lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2819_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2826_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2826_ == 0 {
                        v___x_2821_ = v___x_2809_;
                        v_isShared_2822_ = v_isSharedCheck_2826_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2819_);
                        crate::leanh::lean_dec(v___x_2809_);
                        v___x_2821_ = crate::leanh::lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2826_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2813_ = crate::leanh::lean_box(0);
                if v_isShared_2812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2815_;
            }
            3 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(
    mut v_preNode_2827_: *mut crate::leanh::LeanObject,
    mut v_postNode_2828_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2829_: *mut crate::leanh::LeanObject,
    mut v_t_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2834_ =
        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(
            v_preNode_2827_,
            v_postNode_2828_,
            v_ctx_x3f_2829_,
            v_t_2830_,
            v___y_2831_,
            v___y_2832_,
        );
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    return v_res_2834_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(
    mut v___x_2835_: u8,
    mut v_val_2836_: *mut crate::leanh::LeanObject,
    mut v_val_2837_: *mut crate::leanh::LeanObject,
    mut v_as_2838_: *mut crate::leanh::LeanObject,
    mut v_sz_2839_: usize,
    mut v_i_2840_: usize,
    mut v_b_2841_: *mut crate::leanh::LeanObject,
    mut v___y_2842_: *mut crate::leanh::LeanObject,
    mut v___y_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2845_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: usize = 0;
    let mut v___x_2856_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2845_ = lean_usize_dec_lt(v_i_2840_, v_sz_2839_);
                if v___x_2845_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_2837_);
                    crate::leanh::lean_dec(v_val_2836_);
                    v___x_2846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2846_, 0, v_b_2841_);
                    return v___x_2846_;
                } else {
                    v___x_2847_ = crate::leanh::lean_box((v___x_2835_) as usize);
                    v___f_2848_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_2848_, 0, v___x_2847_);
                    v___x_2849_ = l_Lean_Linter_linter_constructorNameAsVariable;
                    v___x_2850_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_val_2837_);
                    crate::leanh::lean_inc(v_val_2836_);
                    v___f_2851_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed as *mut core::ffi::c_void, 10, 4);
                    crate::leanh::lean_closure_set(v___f_2851_, 0, v_val_2836_);
                    crate::leanh::lean_closure_set(v___f_2851_, 1, v___x_2850_);
                    crate::leanh::lean_closure_set(v___f_2851_, 2, v_val_2837_);
                    crate::leanh::lean_closure_set(v___f_2851_, 3, v___x_2849_);
                    v_a_2852_ = lean_array_uget_borrowed(v_as_2838_, v_i_2840_);
                    v___x_2853_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2852_);
                    v___x_2854_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_2848_, v___f_2851_, v___x_2853_, v_a_2852_, v___y_2842_, v___y_2843_);
                    if crate::leanh::lean_obj_tag(v___x_2854_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2854_, 1);
                        v___x_2855_ = 1usize;
                        v___x_2856_ = lean_usize_add(v_i_2840_, v___x_2855_);
                        v_i_2840_ = v___x_2856_;
                        v_b_2841_ = v___x_2850_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_val_2837_);
                        crate::leanh::lean_dec(v_val_2836_);
                        return v___x_2854_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(
    mut v___x_2858_: *mut crate::leanh::LeanObject,
    mut v_val_2859_: *mut crate::leanh::LeanObject,
    mut v_val_2860_: *mut crate::leanh::LeanObject,
    mut v_as_2861_: *mut crate::leanh::LeanObject,
    mut v_sz_2862_: *mut crate::leanh::LeanObject,
    mut v_i_2863_: *mut crate::leanh::LeanObject,
    mut v_b_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23432__boxed_2868_: u8 = 0;
    let mut v_sz_boxed_2869_: usize = 0;
    let mut v_i_boxed_2870_: usize = 0;
    let mut v_res_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_23432__boxed_2868_ = (crate::leanh::lean_unbox(v___x_2858_) as u8);
    v_sz_boxed_2869_ = crate::leanh::lean_unbox_usize(v_sz_2862_);
    crate::leanh::lean_dec(v_sz_2862_);
    v_i_boxed_2870_ = crate::leanh::lean_unbox_usize(v_i_2863_);
    crate::leanh::lean_dec(v_i_2863_);
    v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23432__boxed_2868_, v_val_2859_, v_val_2860_, v_as_2861_, v_sz_boxed_2869_, v_i_boxed_2870_, v_b_2864_, v___y_2865_, v___y_2866_);
    crate::leanh::lean_dec(v___y_2866_);
    crate::leanh::lean_dec_ref(v___y_2865_);
    crate::leanh::lean_dec_ref(v_as_2861_);
    return v_res_2871_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(
    mut v_x_2872_: *mut crate::leanh::LeanObject,
    mut v_x_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2873_) == 0 {
                    return v_x_2872_;
                } else {
                    v_key_2874_ = crate::leanh::lean_ctor_get(v_x_2873_, 0);
                    v_value_2875_ = crate::leanh::lean_ctor_get(v_x_2873_, 1);
                    v_tail_2876_ = crate::leanh::lean_ctor_get(v_x_2873_, 2);
                    crate::leanh::lean_inc(v_value_2875_);
                    crate::leanh::lean_inc(v_key_2874_);
                    v___x_2877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2877_, 0, v_key_2874_);
                    crate::leanh::lean_ctor_set(v___x_2877_, 1, v_value_2875_);
                    v___x_2878_ = lean_array_push(v_x_2872_, v___x_2877_);
                    v_x_2872_ = v___x_2878_;
                    v_x_2873_ = v_tail_2876_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(
    mut v_x_2880_: *mut crate::leanh::LeanObject,
    mut v_x_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_2880_, v_x_2881_);
    crate::leanh::lean_dec(v_x_2881_);
    return v_res_2882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(
    mut v_as_2883_: *mut crate::leanh::LeanObject,
    mut v_i_2884_: usize,
    mut v_stop_2885_: usize,
    mut v_b_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: usize = 0;
    let mut v___x_2891_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2887_ = lean_usize_dec_eq(v_i_2884_, v_stop_2885_);
                if v___x_2887_ == 0 {
                    v___x_2888_ = lean_array_uget_borrowed(v_as_2883_, v_i_2884_);
                    v___x_2889_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_2886_, v___x_2888_);
                    v___x_2890_ = 1usize;
                    v___x_2891_ = lean_usize_add(v_i_2884_, v___x_2890_);
                    v_i_2884_ = v___x_2891_;
                    v_b_2886_ = v___x_2889_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2886_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(
    mut v_as_2893_: *mut crate::leanh::LeanObject,
    mut v_i_2894_: *mut crate::leanh::LeanObject,
    mut v_stop_2895_: *mut crate::leanh::LeanObject,
    mut v_b_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2897_: usize = 0;
    let mut v_stop_boxed_2898_: usize = 0;
    let mut v_res_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2897_ = crate::leanh::lean_unbox_usize(v_i_2894_);
    crate::leanh::lean_dec(v_i_2894_);
    v_stop_boxed_2898_ = crate::leanh::lean_unbox_usize(v_stop_2895_);
    crate::leanh::lean_dec(v_stop_2895_);
    v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_2893_, v_i_boxed_2897_, v_stop_boxed_2898_, v_b_2896_);
    crate::leanh::lean_dec_ref(v_as_2893_);
    return v_res_2899_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = lean_st_ref_get(v___y_2901_);
    v_scopes_2904_ = crate::leanh::lean_ctor_get(v___x_2903_, 2);
    crate::leanh::lean_inc(v_scopes_2904_);
    crate::leanh::lean_dec(v___x_2903_);
    v___x_2905_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2906_ = l_List_head_x21___redArg(v___x_2905_, v_scopes_2904_);
    crate::leanh::lean_dec(v_scopes_2904_);
    v_opts_2907_ = crate::leanh::lean_ctor_get(v___x_2906_, 1);
    crate::leanh::lean_inc_ref(v_opts_2907_);
    crate::leanh::lean_dec(v___x_2906_);
    v___x_2908_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_2907_, v___y_2901_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(
            v___y_2909_,
            v___y_2910_,
        );
    crate::leanh::lean_dec(v___y_2910_);
    crate::leanh::lean_dec_ref(v___y_2909_);
    return v_res_2912_;
}
pub unsafe fn _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = crate::leanh::lean_box(0);
    v___x_2914_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2915_ = lean_mk_array(v___x_2914_, v___x_2913_);
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once),
        _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0,
    );
    v___x_2917_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2918_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2918_, 0, v___x_2917_);
    crate::leanh::lean_ctor_set(v___x_2918_, 1, v___x_2916_);
    return v___x_2918_;
}
pub unsafe fn l_Lean_Linter_constructorNameAsVariable___lam__0(
    mut v_cmdStx_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2945_: usize = 0;
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2951_: usize = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_unused_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: u8 = 0;
    let mut v_size_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: usize = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2923_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_2920_, v___y_2921_);
                v_a_2924_ = crate::leanh::lean_ctor_get(v___x_2923_, 0);
                v_isSharedCheck_2994_ = (!crate::leanh::lean_is_exclusive(v___x_2923_)) as u8;
                if v_isSharedCheck_2994_ == 0 {
                    v___x_2926_ = v___x_2923_;
                    v_isShared_2927_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2924_);
                    crate::leanh::lean_dec(v___x_2923_);
                    v___x_2926_ = crate::leanh::lean_box(0);
                    v_isShared_2927_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2928_ = l_Lean_Linter_linter_constructorNameAsVariable;
                v___x_2929_ = l_Lean_Linter_getLinterValue(v___x_2928_, v_a_2924_);
                crate::leanh::lean_dec(v_a_2924_);
                if v___x_2929_ == 0 {
                    v___x_2930_ = crate::leanh::lean_box(0);
                    if v_isShared_2927_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2926_, 0, v___x_2930_);
                        v___x_2932_ = v___x_2926_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
                        v___x_2932_ = v_reuseFailAlloc_2933_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2934_ = 0;
                    v___x_2935_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_2919_, v___x_2934_);
                    if crate::leanh::lean_obj_tag(v___x_2935_) == 1 {
                        crate::leanh::lean_del_object(v___x_2926_);
                        v_val_2936_ = crate::leanh::lean_ctor_get(v___x_2935_, 0);
                        crate::leanh::lean_inc(v_val_2936_);
                        crate::leanh::lean_dec_ref_known(v___x_2935_, 1);
                        v___x_2937_ = lean_st_ref_get(v___y_2921_);
                        v___x_2938_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2939_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1,
                        );
                        v___x_2940_ = lean_st_mk_ref(v___x_2939_);
                        v_infoState_2941_ = crate::leanh::lean_ctor_get(v___x_2937_, 8);
                        crate::leanh::lean_inc_ref(v_infoState_2941_);
                        crate::leanh::lean_dec(v___x_2937_);
                        v_trees_2942_ = crate::leanh::lean_ctor_get(v_infoState_2941_, 2);
                        crate::leanh::lean_inc_ref(v_trees_2942_);
                        crate::leanh::lean_dec_ref(v_infoState_2941_);
                        v___x_2943_ = l_Lean_PersistentArray_toArray___redArg(v_trees_2942_);
                        crate::leanh::lean_dec_ref(v_trees_2942_);
                        v___x_2944_ = crate::leanh::lean_box(0);
                        v_sz_2945_ = lean_array_size(v___x_2943_);
                        v___x_2946_ = 0usize;
                        crate::leanh::lean_inc(v___x_2940_);
                        v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_2929_, v___x_2940_, v_val_2936_, v___x_2943_, v_sz_2945_, v___x_2946_, v___x_2944_, v___y_2920_, v___y_2921_);
                        crate::leanh::lean_dec_ref(v___x_2943_);
                        if crate::leanh::lean_obj_tag(v___x_2947_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2947_, 1);
                            v___x_2948_ = lean_st_ref_get(v___x_2940_);
                            crate::leanh::lean_dec(v___x_2940_);
                            v_size_2980_ = crate::leanh::lean_ctor_get(v___x_2948_, 0);
                            crate::leanh::lean_inc(v_size_2980_);
                            v_buckets_2981_ = crate::leanh::lean_ctor_get(v___x_2948_, 1);
                            crate::leanh::lean_inc_ref(v_buckets_2981_);
                            crate::leanh::lean_dec(v___x_2948_);
                            v___x_2982_ = lean_mk_empty_array_with_capacity(v_size_2980_);
                            crate::leanh::lean_dec(v_size_2980_);
                            v___x_2983_ = lean_array_get_size(v_buckets_2981_);
                            v___x_2984_ = lean_nat_dec_lt(v___x_2938_, v___x_2983_);
                            if v___x_2984_ == 0 {
                                crate::leanh::lean_dec_ref(v_buckets_2981_);
                                v___y_2974_ = v___x_2982_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2985_ = lean_nat_dec_le(v___x_2983_, v___x_2983_);
                                if v___x_2985_ == 0 {
                                    if v___x_2984_ == 0 {
                                        crate::leanh::lean_dec_ref(v_buckets_2981_);
                                        v___y_2974_ = v___x_2982_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_2986_ = lean_usize_of_nat(v___x_2983_);
                                        v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_2981_, v___x_2946_, v___x_2986_, v___x_2982_);
                                        crate::leanh::lean_dec_ref(v_buckets_2981_);
                                        v___y_2974_ = v___x_2987_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v___x_2988_ = lean_usize_of_nat(v___x_2983_);
                                    v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_2981_, v___x_2946_, v___x_2988_, v___x_2982_);
                                    crate::leanh::lean_dec_ref(v_buckets_2981_);
                                    v___y_2974_ = v___x_2989_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2940_);
                            return v___x_2947_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2935_);
                        v___x_2990_ = crate::leanh::lean_box(0);
                        if v_isShared_2927_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2926_, 0, v___x_2990_);
                            v___x_2992_ = v___x_2926_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2993_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
                            v___x_2992_ = v_reuseFailAlloc_2993_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2932_;
            }
            3 => {
                v_sz_2951_ = lean_array_size(v___y_2950_);
                v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_2950_, v_sz_2951_, v___x_2946_, v___x_2944_, v___y_2920_, v___y_2921_);
                crate::leanh::lean_dec_ref(v___y_2950_);
                if crate::leanh::lean_obj_tag(v___x_2952_) == 0 {
                    v_isSharedCheck_2959_ = (!crate::leanh::lean_is_exclusive(v___x_2952_)) as u8;
                    if v_isSharedCheck_2959_ == 0 {
                        v_unused_2960_ = crate::leanh::lean_ctor_get(v___x_2952_, 0);
                        crate::leanh::lean_dec(v_unused_2960_);
                        v___x_2954_ = v___x_2952_;
                        v_isShared_2955_ = v_isSharedCheck_2959_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2952_);
                        v___x_2954_ = crate::leanh::lean_box(0);
                        v_isShared_2955_ = v_isSharedCheck_2959_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_2952_;
                }
            }
            4 => {
                if v_isShared_2955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2954_, 0, v___x_2944_);
                    v___x_2957_ = v___x_2954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2944_);
                    v___x_2957_ = v_reuseFailAlloc_2958_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2957_;
            }
            6 => {
                v___x_2966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_2962_, v___y_2964_, v___y_2963_, v___y_2965_);
                crate::leanh::lean_dec(v___y_2965_);
                crate::leanh::lean_dec(v___y_2962_);
                v___y_2950_ = v___x_2966_;
                state = 3;
                continue;
            }
            7 => {
                v___x_2972_ = lean_nat_dec_le(v___y_2971_, v___y_2969_);
                if v___x_2972_ == 0 {
                    crate::leanh::lean_dec(v___y_2969_);
                    crate::leanh::lean_inc(v___y_2971_);
                    v___y_2962_ = v___y_2968_;
                    v___y_2963_ = v___y_2971_;
                    v___y_2964_ = v___y_2970_;
                    v___y_2965_ = v___y_2971_;
                    state = 6;
                    continue;
                } else {
                    v___y_2962_ = v___y_2968_;
                    v___y_2963_ = v___y_2971_;
                    v___y_2964_ = v___y_2970_;
                    v___y_2965_ = v___y_2969_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_2975_ = lean_array_get_size(v___y_2974_);
                v___x_2976_ = lean_nat_dec_eq(v___x_2975_, v___x_2938_);
                if v___x_2976_ == 0 {
                    v___x_2977_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2978_ = lean_nat_sub(v___x_2975_, v___x_2977_);
                    v___x_2979_ = lean_nat_dec_le(v___x_2938_, v___x_2978_);
                    if v___x_2979_ == 0 {
                        crate::leanh::lean_inc(v___x_2978_);
                        v___y_2968_ = v___x_2975_;
                        v___y_2969_ = v___x_2978_;
                        v___y_2970_ = v___y_2974_;
                        v___y_2971_ = v___x_2978_;
                        state = 7;
                        continue;
                    } else {
                        v___y_2968_ = v___x_2975_;
                        v___y_2969_ = v___x_2978_;
                        v___y_2970_ = v___y_2974_;
                        v___y_2971_ = v___x_2938_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_2950_ = v___y_2974_;
                    state = 3;
                    continue;
                }
            }
            9 => {
                return v___x_2992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(
    mut v_cmdStx_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2999_ =
        l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_2995_, v___y_2996_, v___y_2997_);
    crate::leanh::lean_dec(v___y_2997_);
    crate::leanh::lean_dec_ref(v___y_2996_);
    crate::leanh::lean_dec(v_cmdStx_2995_);
    return v_res_2999_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(
    mut v_00_u03b2_3009_: *mut crate::leanh::LeanObject,
    mut v_m_3010_: *mut crate::leanh::LeanObject,
    mut v_a_3011_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3012_: u8 = 0;
    v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_3010_, v_a_3011_);
    return v___x_3012_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(
    mut v_00_u03b2_3013_: *mut crate::leanh::LeanObject,
    mut v_m_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3016_: u8 = 0;
    let mut v_r_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_3013_, v_m_3014_, v_a_3015_);
    crate::leanh::lean_dec_ref(v_a_3015_);
    crate::leanh::lean_dec_ref(v_m_3014_);
    v_r_3017_ = crate::leanh::lean_box((v_res_3016_) as usize);
    return v_r_3017_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(
    mut v_00_u03b2_3018_: *mut crate::leanh::LeanObject,
    mut v_m_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_b_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3022_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_3019_, v_a_3020_, v_b_3021_);
    return v___x_3022_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(
    mut v_str_3023_: *mut crate::leanh::LeanObject,
    mut v_val_3024_: *mut crate::leanh::LeanObject,
    mut v_info_3025_: *mut crate::leanh::LeanObject,
    mut v___x_3026_: *mut crate::leanh::LeanObject,
    mut v_val_3027_: *mut crate::leanh::LeanObject,
    mut v___x_3028_: u8,
    mut v_as_3029_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3030_: *mut crate::leanh::LeanObject,
    mut v_b_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(
            v_str_3023_,
            v_val_3024_,
            v_info_3025_,
            v___x_3026_,
            v_val_3027_,
            v___x_3028_,
            v_as_x27_3030_,
            v_b_3031_,
            v___y_3034_,
        );
    return v___x_3036_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(
    mut v_str_3037_: *mut crate::leanh::LeanObject,
    mut v_val_3038_: *mut crate::leanh::LeanObject,
    mut v_info_3039_: *mut crate::leanh::LeanObject,
    mut v___x_3040_: *mut crate::leanh::LeanObject,
    mut v_val_3041_: *mut crate::leanh::LeanObject,
    mut v___x_3042_: *mut crate::leanh::LeanObject,
    mut v_as_3043_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3044_: *mut crate::leanh::LeanObject,
    mut v_b_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23724__boxed_3050_: u8 = 0;
    let mut v_res_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_23724__boxed_3050_ = (crate::leanh::lean_unbox(v___x_3042_) as u8);
    v_res_3051_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(
        v_str_3037_,
        v_val_3038_,
        v_info_3039_,
        v___x_3040_,
        v_val_3041_,
        v___x_23724__boxed_3050_,
        v_as_3043_,
        v_as_x27_3044_,
        v_b_3045_,
        v_a_3046_,
        v___y_3047_,
        v___y_3048_,
    );
    crate::leanh::lean_dec(v___y_3048_);
    crate::leanh::lean_dec_ref(v___y_3047_);
    crate::leanh::lean_dec(v_as_x27_3044_);
    crate::leanh::lean_dec(v_as_3043_);
    crate::leanh::lean_dec_ref(v_info_3039_);
    crate::leanh::lean_dec(v_val_3038_);
    crate::leanh::lean_dec_ref(v_str_3037_);
    return v_res_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(
    mut v_n_3052_: *mut crate::leanh::LeanObject,
    mut v_as_3053_: *mut crate::leanh::LeanObject,
    mut v_lo_3054_: *mut crate::leanh::LeanObject,
    mut v_hi_3055_: *mut crate::leanh::LeanObject,
    mut v_w_3056_: *mut crate::leanh::LeanObject,
    mut v_hlo_3057_: *mut crate::leanh::LeanObject,
    mut v_hhi_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_3052_, v_as_3053_, v_lo_3054_, v_hi_3055_);
    return v___x_3059_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(
    mut v_n_3060_: *mut crate::leanh::LeanObject,
    mut v_as_3061_: *mut crate::leanh::LeanObject,
    mut v_lo_3062_: *mut crate::leanh::LeanObject,
    mut v_hi_3063_: *mut crate::leanh::LeanObject,
    mut v_w_3064_: *mut crate::leanh::LeanObject,
    mut v_hlo_3065_: *mut crate::leanh::LeanObject,
    mut v_hhi_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_3060_, v_as_3061_, v_lo_3062_, v_hi_3063_, v_w_3064_, v_hlo_3065_, v_hhi_3066_);
    crate::leanh::lean_dec(v_hi_3063_);
    crate::leanh::lean_dec(v_n_3060_);
    return v_res_3067_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(
    mut v_00_u03b2_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3071_: u8 = 0;
    v___x_3071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_3069_, v_x_3070_);
    return v___x_3071_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(
    mut v_00_u03b2_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_x_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3075_: u8 = 0;
    let mut v_r_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_3072_, v_a_3073_, v_x_3074_);
    crate::leanh::lean_dec(v_x_3074_);
    crate::leanh::lean_dec_ref(v_a_3073_);
    v_r_3076_ = crate::leanh::lean_box((v_res_3075_) as usize);
    return v_r_3076_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(
    mut v_00_u03b2_3077_: *mut crate::leanh::LeanObject,
    mut v_data_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_3078_);
    return v___x_3079_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(
    mut v_00_u03b2_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_b_3082_: *mut crate::leanh::LeanObject,
    mut v_x_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_3081_, v_b_3082_, v_x_3083_);
    return v___x_3084_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(
    mut v_00_u03b1_3085_: *mut crate::leanh::LeanObject,
    mut v_msg_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_3086_, v___y_3087_, v___y_3088_);
    return v___x_3090_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(
    mut v_00_u03b1_3091_: *mut crate::leanh::LeanObject,
    mut v_msg_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_3091_, v_msg_3092_, v___y_3093_, v___y_3094_);
    crate::leanh::lean_dec(v___y_3094_);
    crate::leanh::lean_dec_ref(v___y_3093_);
    return v_res_3096_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(
    mut v_00_u03b1_3097_: *mut crate::leanh::LeanObject,
    mut v_preNode_3098_: *mut crate::leanh::LeanObject,
    mut v_postNode_3099_: *mut crate::leanh::LeanObject,
    mut v_x_3100_: *mut crate::leanh::LeanObject,
    mut v_x_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_3098_, v_postNode_3099_, v_x_3100_, v_x_3101_, v___y_3102_, v___y_3103_);
    return v___x_3105_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(
    mut v_00_u03b1_3106_: *mut crate::leanh::LeanObject,
    mut v_preNode_3107_: *mut crate::leanh::LeanObject,
    mut v_postNode_3108_: *mut crate::leanh::LeanObject,
    mut v_x_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_3106_, v_preNode_3107_, v_postNode_3108_, v_x_3109_, v_x_3110_, v___y_3111_, v___y_3112_);
    crate::leanh::lean_dec(v___y_3112_);
    crate::leanh::lean_dec_ref(v___y_3111_);
    return v_res_3114_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(
    mut v_n_3115_: *mut crate::leanh::LeanObject,
    mut v_lo_3116_: *mut crate::leanh::LeanObject,
    mut v_hi_3117_: *mut crate::leanh::LeanObject,
    mut v_hhi_3118_: *mut crate::leanh::LeanObject,
    mut v_pivot_3119_: *mut crate::leanh::LeanObject,
    mut v_as_3120_: *mut crate::leanh::LeanObject,
    mut v_i_3121_: *mut crate::leanh::LeanObject,
    mut v_k_3122_: *mut crate::leanh::LeanObject,
    mut v_ilo_3123_: *mut crate::leanh::LeanObject,
    mut v_ik_3124_: *mut crate::leanh::LeanObject,
    mut v_w_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_3117_, v_pivot_3119_, v_as_3120_, v_i_3121_, v_k_3122_);
    return v___x_3126_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(
    mut v_n_3127_: *mut crate::leanh::LeanObject,
    mut v_lo_3128_: *mut crate::leanh::LeanObject,
    mut v_hi_3129_: *mut crate::leanh::LeanObject,
    mut v_hhi_3130_: *mut crate::leanh::LeanObject,
    mut v_pivot_3131_: *mut crate::leanh::LeanObject,
    mut v_as_3132_: *mut crate::leanh::LeanObject,
    mut v_i_3133_: *mut crate::leanh::LeanObject,
    mut v_k_3134_: *mut crate::leanh::LeanObject,
    mut v_ilo_3135_: *mut crate::leanh::LeanObject,
    mut v_ik_3136_: *mut crate::leanh::LeanObject,
    mut v_w_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_3127_, v_lo_3128_, v_hi_3129_, v_hhi_3130_, v_pivot_3131_, v_as_3132_, v_i_3133_, v_k_3134_, v_ilo_3135_, v_ik_3136_, v_w_3137_);
    crate::leanh::lean_dec_ref(v_pivot_3131_);
    crate::leanh::lean_dec(v_hi_3129_);
    crate::leanh::lean_dec(v_lo_3128_);
    crate::leanh::lean_dec(v_n_3127_);
    return v_res_3138_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(
    mut v_00_u03b2_3139_: *mut crate::leanh::LeanObject,
    mut v_i_3140_: *mut crate::leanh::LeanObject,
    mut v_source_3141_: *mut crate::leanh::LeanObject,
    mut v_target_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3143_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_3140_, v_source_3141_, v_target_3142_);
    return v___x_3143_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(
    mut v_00_u03b1_3144_: *mut crate::leanh::LeanObject,
    mut v_preNode_3145_: *mut crate::leanh::LeanObject,
    mut v_postNode_3146_: *mut crate::leanh::LeanObject,
    mut v___x_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v_x_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3153_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_3145_, v_postNode_3146_, v___x_3147_, v_x_3148_, v_x_3149_, v___y_3150_, v___y_3151_);
    return v___x_3153_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(
    mut v_00_u03b1_3154_: *mut crate::leanh::LeanObject,
    mut v_preNode_3155_: *mut crate::leanh::LeanObject,
    mut v_postNode_3156_: *mut crate::leanh::LeanObject,
    mut v___x_3157_: *mut crate::leanh::LeanObject,
    mut v_x_3158_: *mut crate::leanh::LeanObject,
    mut v_x_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3163_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_3154_, v_preNode_3155_, v_postNode_3156_, v___x_3157_, v_x_3158_, v_x_3159_, v___y_3160_, v___y_3161_);
    crate::leanh::lean_dec(v___y_3161_);
    crate::leanh::lean_dec_ref(v___y_3160_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(
    mut v_msgData_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_3164_, v___y_3166_);
    return v___x_3168_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(
    mut v_msgData_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_3169_, v___y_3170_, v___y_3171_);
    crate::leanh::lean_dec(v___y_3171_);
    crate::leanh::lean_dec_ref(v___y_3170_);
    return v_res_3173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(
    mut v_00_u03b2_3174_: *mut crate::leanh::LeanObject,
    mut v_x_3175_: *mut crate::leanh::LeanObject,
    mut v_x_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_3175_, v_x_3176_);
    return v___x_3177_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_Linter_constructorNameAsVariable;
    v___x_3180_ = l_Lean_Elab_Command_addLinter(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(
    mut v_a_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3182_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
    return v_res_3182_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_ConstructorAsVariable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_constructorNameAsVariable = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_constructorNameAsVariable);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_ConstructorAsVariable(
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
pub unsafe fn initialize_Lean_Linter_ConstructorAsVariable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_ConstructorAsVariable(builtin);
}
