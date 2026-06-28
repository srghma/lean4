// Lean compiler output
// Module: Lean.Linter.UnusedSimpArgs
// Imports: Lean.Elab.Command Lean.Elab.Tactic.Simp Lean.Linter.Util
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_toArray___redArg, l_Lean_PersistentArray_toList___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed,
    l_Lean_Elab_Command_liftCoreM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_Info_updateContext_x3f, l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, l_Lean_Elab_Tactic_getSimpParams,
    l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_,
    l_Lean_Elab_Tactic_linter_unusedSimpArgs, l_Lean_Elab_Tactic_setSimpParams,
    runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Hint::l_Lean_MessageData_hint;
use crate::r#gen::Lean::Server::InfoUtils::{l_Lean_Elab_Info_range_x3f, l_Lean_Elab_Info_stx};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instBEqRange_beq,
    l_Lean_Syntax_instHashableRange_hash,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value:
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
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value:
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
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        16145843736367156323 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value:
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
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value:
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
        79, 109, 105, 116, 32, 105, 116, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 115, 105,
        109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 108, 105, 115, 116, 46, 0,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        84, 104, 105, 115, 32, 115, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32,
        105, 115, 32, 117, 110, 117, 115, 101, 100, 58, 0,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value:
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
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value:
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
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value:
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
    m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0:
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
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value) as *mut crate::leanh::LeanObject,7383208167966365478 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value:
    crate::leanh::LeanStringObject<260> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 260,
    m_capacity: 260,
    m_length: 255,
    m_data: [
        83, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 119, 105, 116, 104,
        32, 96, 226, 134, 144, 96, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 97, 100, 100, 105,
        116, 105, 111, 110, 97, 108, 32, 101, 102, 102, 101, 99, 116, 32, 111, 102, 32, 114, 101,
        109, 111, 118, 105, 110, 103, 32, 116, 104, 101, 32, 111, 116, 104, 101, 114, 32, 100, 105,
        114, 101, 99, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 115, 105,
        109, 112, 32, 115, 101, 116, 44, 32, 101, 118, 101, 110, 32, 105, 102, 32, 116, 104, 101,
        32, 115, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 116, 115, 101,
        108, 102, 32, 105, 115, 32, 117, 110, 117, 115, 101, 100, 46, 32, 73, 102, 32, 116, 104,
        101, 32, 104, 105, 110, 116, 32, 97, 98, 111, 118, 101, 32, 100, 111, 101, 115, 32, 110,
        111, 116, 32, 119, 111, 114, 107, 44, 32, 116, 114, 121, 32, 114, 101, 112, 108, 97, 99,
        105, 110, 103, 32, 96, 226, 134, 144, 96, 32, 119, 105, 116, 104, 32, 96, 45, 96, 32, 116,
        111, 32, 111, 110, 108, 121, 32, 103, 101, 116, 32, 116, 104, 97, 116, 32, 101, 102, 102,
        101, 99, 116, 32, 97, 110, 100, 32, 115, 105, 108, 101, 110, 99, 101, 32, 116, 104, 105,
        115, 32, 119, 97, 114, 110, 105, 110, 103, 46, 0,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value:
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
    m_data: [73, 110, 100, 101, 120, 32, 0],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 32, 102, 111, 114, 32,
        115, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 111, 102, 32, 0,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [83, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 109, 97, 115, 107, 32, 115, 105, 122, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 125, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 118, 115, 46, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 65, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,17985617252278808837 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value) as *mut crate::leanh::LeanObject,12783917532758215986 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_unusedSimpArgs___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_unusedSimpArgs___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [76, 105, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__2_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            117, 110, 117, 115, 101, 100, 83, 105, 109, 112, 65, 114, 103, 115, 0,
        ],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8071394701935581384 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Linter_unusedSimpArgs___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            14321273934322160490 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_unusedSimpArgs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(
    mut v_upperBound_1776_: *mut crate::leanh::LeanObject,
    mut v_i_1777_: *mut crate::leanh::LeanObject,
    mut v_simpArgs_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_b_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1787_ = lean_nat_dec_lt(v_a_1779_, v_upperBound_1776_);
                if v___x_1787_ == 0 {
                    crate::leanh::lean_dec(v_a_1779_);
                    v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1788_, 0, v_b_1780_);
                    return v___x_1788_;
                } else {
                    v___x_1789_ = lean_nat_dec_eq(v_a_1779_, v_i_1777_);
                    if v___x_1789_ == 0 {
                        v___x_1790_ = lean_array_fget_borrowed(v_simpArgs_1778_, v_a_1779_);
                        crate::leanh::lean_inc(v___x_1790_);
                        v___x_1791_ = lean_array_push(v_b_1780_, v___x_1790_);
                        v_a_1783_ = v___x_1791_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1783_ = v_b_1780_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1784_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1785_ = lean_nat_add(v_a_1779_, v___x_1784_);
                crate::leanh::lean_dec(v_a_1779_);
                v_a_1779_ = v___x_1785_;
                v_b_1780_ = v_a_1783_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg___boxed(
    mut v_upperBound_1792_: *mut crate::leanh::LeanObject,
    mut v_i_1793_: *mut crate::leanh::LeanObject,
    mut v_simpArgs_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_b_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_1792_, v_i_1793_, v_simpArgs_1794_, v_a_1795_, v_b_1796_);
    crate::leanh::lean_dec_ref(v_simpArgs_1794_);
    crate::leanh::lean_dec(v_i_1793_);
    crate::leanh::lean_dec(v_upperBound_1792_);
    return v_res_1798_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1799_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0);
    v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
    v___x_1803_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1804_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 3, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 4, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 5, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 6, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 7, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 8, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 9, v___x_1802_);
    return v___x_1804_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
    v___x_1807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = 5usize;
    v___x_1809_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1810_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
    v___x_1812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1813_, 2, v___x_1809_);
    crate::leanh::lean_ctor_set(v___x_1813_, 3, v___x_1809_);
    crate::leanh::lean_ctor_set_usize(v___x_1813_, 4, v___x_1808_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = crate::leanh::lean_box(1);
    v___x_1815_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4);
    v___x_1816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
    v___x_1817_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1815_);
    crate::leanh::lean_ctor_set(v___x_1817_, 2, v___x_1814_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(
    mut v_msgData_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_st_ref_get(v___y_1820_);
    v_env_1823_ = crate::leanh::lean_ctor_get(v___x_1822_, 0);
    crate::leanh::lean_inc_ref(v_env_1823_);
    crate::leanh::lean_dec(v___x_1822_);
    v_options_1824_ = crate::leanh::lean_ctor_get(v___y_1819_, 2);
    v___x_1825_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
    v___x_1826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
    crate::leanh::lean_inc_ref(v_options_1824_);
    v___x_1827_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1827_, 0, v_env_1823_);
    crate::leanh::lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    crate::leanh::lean_ctor_set(v___x_1827_, 2, v___x_1826_);
    crate::leanh::lean_ctor_set(v___x_1827_, 3, v_options_1824_);
    v___x_1828_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1828_, 0, v___x_1827_);
    crate::leanh::lean_ctor_set(v___x_1828_, 1, v_msgData_1818_);
    v___x_1829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(
    mut v_msgData_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_1830_, v___y_1831_, v___y_1832_);
    crate::leanh::lean_dec(v___y_1832_);
    crate::leanh::lean_dec_ref(v___y_1831_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(
    mut v_msg_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1839_ = crate::leanh::lean_ctor_get(v___y_1836_, 5);
                v___x_1840_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_1835_, v___y_1836_, v___y_1837_);
                v_a_1841_ = crate::leanh::lean_ctor_get(v___x_1840_, 0);
                v_isSharedCheck_1849_ = (!crate::leanh::lean_is_exclusive(v___x_1840_)) as u8;
                if v_isSharedCheck_1849_ == 0 {
                    v___x_1843_ = v___x_1840_;
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1841_);
                    crate::leanh::lean_dec(v___x_1840_);
                    v___x_1843_ = crate::leanh::lean_box(0);
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1839_);
                v___x_1845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1845_, 0, v_ref_1839_);
                crate::leanh::lean_ctor_set(v___x_1845_, 1, v_a_1841_);
                if v_isShared_1844_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1843_, 1);
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1845_);
                    v___x_1847_ = v___x_1843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(
    mut v_msg_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_1850_, v___y_1851_, v___y_1852_);
    crate::leanh::lean_dec(v___y_1852_);
    crate::leanh::lean_dec_ref(v___y_1851_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(
    mut v___y_1863_: u8,
    mut v_suppressElabErrors_1864_: u8,
    mut v_x_1865_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1865_) == 1 {
        let mut v_pre_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1866_ = crate::leanh::lean_ctor_get(v_x_1865_, 0);
        match crate::leanh::lean_obj_tag(v_pre_1866_) {
            1 => {
                let mut v_pre_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_1867_ = crate::leanh::lean_ctor_get(v_pre_1866_, 0);
                match crate::leanh::lean_obj_tag(v_pre_1867_) {
                    0 => {
                        let mut v_str_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1871_: u8 = 0;
                        v_str_1868_ = crate::leanh::lean_ctor_get(v_x_1865_, 1);
                        v_str_1869_ = crate::leanh::lean_ctor_get(v_pre_1866_, 1);
                        v___x_1870_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_1871_ = lean_string_dec_eq(v_str_1869_, v___x_1870_);
                        if v___x_1871_ == 0 {
                            let mut v___x_1872_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1873_: u8 = 0;
                            v___x_1872_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_1873_ = lean_string_dec_eq(v_str_1869_, v___x_1872_);
                            if v___x_1873_ == 0 {
                                return v___y_1863_;
                            } else {
                                let mut v___x_1874_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1875_: u8 = 0;
                                v___x_1874_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2;
                                v___x_1875_ = lean_string_dec_eq(v_str_1868_, v___x_1874_);
                                if v___x_1875_ == 0 {
                                    return v___y_1863_;
                                } else {
                                    return v_suppressElabErrors_1864_;
                                }
                            }
                        } else {
                            let mut v___x_1876_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1877_: u8 = 0;
                            v___x_1876_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_1877_ = lean_string_dec_eq(v_str_1868_, v___x_1876_);
                            if v___x_1877_ == 0 {
                                return v___y_1863_;
                            } else {
                                return v_suppressElabErrors_1864_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1878_ = crate::leanh::lean_ctor_get(v_pre_1867_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_1878_) == 0 {
                            let mut v_str_1879_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1880_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1881_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1882_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1883_: u8 = 0;
                            v_str_1879_ = crate::leanh::lean_ctor_get(v_x_1865_, 1);
                            v_str_1880_ = crate::leanh::lean_ctor_get(v_pre_1866_, 1);
                            v_str_1881_ = crate::leanh::lean_ctor_get(v_pre_1867_, 1);
                            v___x_1882_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_1883_ = lean_string_dec_eq(v_str_1881_, v___x_1882_);
                            if v___x_1883_ == 0 {
                                return v___y_1863_;
                            } else {
                                let mut v___x_1884_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1885_: u8 = 0;
                                v___x_1884_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_1885_ = lean_string_dec_eq(v_str_1880_, v___x_1884_);
                                if v___x_1885_ == 0 {
                                    return v___y_1863_;
                                } else {
                                    let mut v___x_1886_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1887_: u8 = 0;
                                    v___x_1886_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6;
                                    v___x_1887_ = lean_string_dec_eq(v_str_1879_, v___x_1886_);
                                    if v___x_1887_ == 0 {
                                        return v___y_1863_;
                                    } else {
                                        return v_suppressElabErrors_1864_;
                                    }
                                }
                            }
                        } else {
                            return v___y_1863_;
                        }
                    }
                    _ => {
                        return v___y_1863_;
                    }
                }
            }
            0 => {
                let mut v_str_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1890_: u8 = 0;
                v_str_1888_ = crate::leanh::lean_ctor_get(v_x_1865_, 1);
                v___x_1889_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7;
                v___x_1890_ = lean_string_dec_eq(v_str_1888_, v___x_1889_);
                if v___x_1890_ == 0 {
                    return v___y_1863_;
                } else {
                    return v_suppressElabErrors_1864_;
                }
            }
            _ => {
                return v___y_1863_;
            }
        }
    } else {
        return v___y_1863_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1892_: *mut crate::leanh::LeanObject,
    mut v_x_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4604__boxed_1894_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1895_: u8 = 0;
    let mut v_res_1896_: u8 = 0;
    let mut v_r_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4604__boxed_1894_ = (crate::leanh::lean_unbox(v___y_1891_) as u8);
    v_suppressElabErrors_boxed_1895_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1892_) as u8);
    v_res_1896_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v___y_4604__boxed_1894_, v_suppressElabErrors_boxed_1895_, v_x_1893_);
    crate::leanh::lean_dec(v_x_1893_);
    v_r_1897_ = crate::leanh::lean_box((v_res_1896_) as usize);
    return v_r_1897_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(
    mut v_opts_1898_: *mut crate::leanh::LeanObject,
    mut v_opt_1899_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1900_ = crate::leanh::lean_ctor_get(v_opt_1899_, 0);
    v_defValue_1901_ = crate::leanh::lean_ctor_get(v_opt_1899_, 1);
    v_map_1902_ = crate::leanh::lean_ctor_get(v_opts_1898_, 0);
    v___x_1903_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1902_,
            v_name_1900_,
        );
    if crate::leanh::lean_obj_tag(v___x_1903_) == 0 {
        let mut v___x_1904_: u8 = 0;
        v___x_1904_ = (crate::leanh::lean_unbox(v_defValue_1901_) as u8);
        return v___x_1904_;
    } else {
        let mut v_val_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1905_ = crate::leanh::lean_ctor_get(v___x_1903_, 0);
        crate::leanh::lean_inc(v_val_1905_);
        crate::leanh::lean_dec_ref_known(v___x_1903_, 1);
        if crate::leanh::lean_obj_tag(v_val_1905_) == 1 {
            let mut v_v_1906_: u8 = 0;
            v_v_1906_ = crate::leanh::lean_ctor_get_uint8(v_val_1905_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1905_, 0);
            return v_v_1906_;
        } else {
            let mut v___x_1907_: u8 = 0;
            crate::leanh::lean_dec(v_val_1905_);
            v___x_1907_ = (crate::leanh::lean_unbox(v_defValue_1901_) as u8);
            return v___x_1907_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_opts_1908_: *mut crate::leanh::LeanObject,
    mut v_opt_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: u8 = 0;
    let mut v_r_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_1908_, v_opt_1909_);
    crate::leanh::lean_dec_ref(v_opt_1909_);
    crate::leanh::lean_dec_ref(v_opts_1908_);
    v_r_1911_ = crate::leanh::lean_box((v_res_1910_) as usize);
    return v_r_1911_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(
    mut v_ref_1913_: *mut crate::leanh::LeanObject,
    mut v_msgData_1914_: *mut crate::leanh::LeanObject,
    mut v_severity_1915_: u8,
    mut v_isSilent_1916_: u8,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: u8 = 0;
    let mut v___y_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: u8 = 0;
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v___y_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1959_: u8 = 0;
    let mut v___y_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: u8 = 0;
    let mut v___y_1962_: u8 = 0;
    let mut v___y_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v___y_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: u8 = 0;
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: u8 = 0;
    let mut v___y_1988_: u8 = 0;
    let mut v___y_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: u8 = 0;
    let mut v___y_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: u8 = 0;
    let mut v___y_1999_: u8 = 0;
    let mut v_ref_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: u8 = 0;
    let mut v___y_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: u8 = 0;
    let mut v___y_2012_: u8 = 0;
    let mut v___y_2014_: u8 = 0;
    let mut v_fileName_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2004_ = 2;
                v___x_2029_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1915_, v___x_2004_);
                if v___x_2029_ == 0 {
                    v___y_2014_ = v___x_2029_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1914_);
                    v___x_2030_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1914_);
                    v___y_2014_ = v___x_2030_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1930_ = lean_st_ref_take(v___y_1929_);
                v_currNamespace_1931_ = crate::leanh::lean_ctor_get(v___y_1928_, 6);
                v_openDecls_1932_ = crate::leanh::lean_ctor_get(v___y_1928_, 7);
                v_env_1933_ = crate::leanh::lean_ctor_get(v___x_1930_, 0);
                v_nextMacroScope_1934_ = crate::leanh::lean_ctor_get(v___x_1930_, 1);
                v_ngen_1935_ = crate::leanh::lean_ctor_get(v___x_1930_, 2);
                v_auxDeclNGen_1936_ = crate::leanh::lean_ctor_get(v___x_1930_, 3);
                v_traceState_1937_ = crate::leanh::lean_ctor_get(v___x_1930_, 4);
                v_cache_1938_ = crate::leanh::lean_ctor_get(v___x_1930_, 5);
                v_messages_1939_ = crate::leanh::lean_ctor_get(v___x_1930_, 6);
                v_infoState_1940_ = crate::leanh::lean_ctor_get(v___x_1930_, 7);
                v_snapshotTasks_1941_ = crate::leanh::lean_ctor_get(v___x_1930_, 8);
                v_isSharedCheck_1955_ = (!crate::leanh::lean_is_exclusive(v___x_1930_)) as u8;
                if v_isSharedCheck_1955_ == 0 {
                    v___x_1943_ = v___x_1930_;
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1941_);
                    crate::leanh::lean_inc(v_infoState_1940_);
                    crate::leanh::lean_inc(v_messages_1939_);
                    crate::leanh::lean_inc(v_cache_1938_);
                    crate::leanh::lean_inc(v_traceState_1937_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1936_);
                    crate::leanh::lean_inc(v_ngen_1935_);
                    crate::leanh::lean_inc(v_nextMacroScope_1934_);
                    crate::leanh::lean_inc(v_env_1933_);
                    crate::leanh::lean_dec(v___x_1930_);
                    v___x_1943_ = crate::leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_1932_);
                crate::leanh::lean_inc(v_currNamespace_1931_);
                v___x_1945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1945_, 0, v_currNamespace_1931_);
                crate::leanh::lean_ctor_set(v___x_1945_, 1, v_openDecls_1932_);
                v___x_1946_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1945_);
                crate::leanh::lean_ctor_set(v___x_1946_, 1, v___y_1925_);
                crate::leanh::lean_inc_ref(v___y_1926_);
                crate::leanh::lean_inc_ref(v___y_1923_);
                v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1947_, 0, v___y_1923_);
                crate::leanh::lean_ctor_set(v___x_1947_, 1, v___y_1922_);
                crate::leanh::lean_ctor_set(v___x_1947_, 2, v___y_1921_);
                crate::leanh::lean_ctor_set(v___x_1947_, 3, v___y_1926_);
                crate::leanh::lean_ctor_set(v___x_1947_, 4, v___x_1946_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1927_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1924_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1916_,
                );
                v___x_1948_ = l_Lean_MessageLog_add(v___x_1947_, v_messages_1939_);
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1943_, 6, v___x_1948_);
                    v___x_1950_ = v___x_1943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_env_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_nextMacroScope_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_ngen_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_auxDeclNGen_1936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_traceState_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 5, v_cache_1938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 6, v___x_1948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 7, v_infoState_1940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 8, v_snapshotTasks_1941_);
                    v___x_1950_ = v_reuseFailAlloc_1954_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1951_ = lean_st_ref_set(v___y_1929_, v___x_1950_);
                v___x_1952_ = crate::leanh::lean_box(0);
                v___x_1953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1953_, 0, v___x_1952_);
                return v___x_1953_;
            }
            4 => {
                v___x_1965_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1914_,
                    );
                v___x_1966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_1965_, v___y_1917_, v___y_1918_);
                v_a_1967_ = crate::leanh::lean_ctor_get(v___x_1966_, 0);
                v_isSharedCheck_1980_ = (!crate::leanh::lean_is_exclusive(v___x_1966_)) as u8;
                if v_isSharedCheck_1980_ == 0 {
                    v___x_1969_ = v___x_1966_;
                    v_isShared_1970_ = v_isSharedCheck_1980_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1967_);
                    crate::leanh::lean_dec(v___x_1966_);
                    v___x_1969_ = crate::leanh::lean_box(0);
                    v_isShared_1970_ = v_isSharedCheck_1980_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_1958_, 2);
                v___x_1971_ = l_Lean_FileMap_toPosition(v___y_1958_, v___y_1963_);
                crate::leanh::lean_dec(v___y_1963_);
                v___x_1972_ = l_Lean_FileMap_toPosition(v___y_1958_, v___y_1964_);
                crate::leanh::lean_dec(v___y_1964_);
                v___x_1973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1973_, 0, v___x_1972_);
                v___x_1974_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0;
                if v___y_1959_ == 0 {
                    crate::leanh::lean_del_object(v___x_1969_);
                    crate::leanh::lean_dec_ref(v___y_1957_);
                    v___y_1921_ = v___x_1973_;
                    v___y_1922_ = v___x_1971_;
                    v___y_1923_ = v___y_1960_;
                    v___y_1924_ = v___y_1961_;
                    v___y_1925_ = v_a_1967_;
                    v___y_1926_ = v___x_1974_;
                    v___y_1927_ = v___y_1962_;
                    v___y_1928_ = v___y_1917_;
                    v___y_1929_ = v___y_1918_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1967_);
                    v___x_1975_ = l_Lean_MessageData_hasTag(v___y_1957_, v_a_1967_);
                    if v___x_1975_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1973_, 1);
                        crate::leanh::lean_dec_ref(v___x_1971_);
                        crate::leanh::lean_dec(v_a_1967_);
                        v___x_1976_ = crate::leanh::lean_box(0);
                        if v_isShared_1970_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1969_, 0, v___x_1976_);
                            v___x_1978_ = v___x_1969_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1979_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
                            v___x_1978_ = v_reuseFailAlloc_1979_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1969_);
                        v___y_1921_ = v___x_1973_;
                        v___y_1922_ = v___x_1971_;
                        v___y_1923_ = v___y_1960_;
                        v___y_1924_ = v___y_1961_;
                        v___y_1925_ = v_a_1967_;
                        v___y_1926_ = v___x_1974_;
                        v___y_1927_ = v___y_1962_;
                        v___y_1928_ = v___y_1917_;
                        v___y_1929_ = v___y_1918_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1978_;
            }
            7 => {
                v___x_1990_ = l_Lean_Syntax_getTailPos_x3f(v___y_1983_, v___y_1988_);
                crate::leanh::lean_dec(v___y_1983_);
                if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                    crate::leanh::lean_inc(v___y_1989_);
                    v___y_1957_ = v___y_1982_;
                    v___y_1958_ = v___y_1984_;
                    v___y_1959_ = v___y_1985_;
                    v___y_1960_ = v___y_1986_;
                    v___y_1961_ = v___y_1987_;
                    v___y_1962_ = v___y_1988_;
                    v___y_1963_ = v___y_1989_;
                    v___y_1964_ = v___y_1989_;
                    state = 4;
                    continue;
                } else {
                    v_val_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                    crate::leanh::lean_inc(v_val_1991_);
                    crate::leanh::lean_dec_ref_known(v___x_1990_, 1);
                    v___y_1957_ = v___y_1982_;
                    v___y_1958_ = v___y_1984_;
                    v___y_1959_ = v___y_1985_;
                    v___y_1960_ = v___y_1986_;
                    v___y_1961_ = v___y_1987_;
                    v___y_1962_ = v___y_1988_;
                    v___y_1963_ = v___y_1989_;
                    v___y_1964_ = v_val_1991_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2000_ = l_Lean_replaceRef(v_ref_1913_, v___y_1997_);
                v___x_2001_ = l_Lean_Syntax_getPos_x3f(v_ref_2000_, v___y_1998_);
                if crate::leanh::lean_obj_tag(v___x_2001_) == 0 {
                    v___x_2002_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1982_ = v___y_1993_;
                    v___y_1983_ = v_ref_2000_;
                    v___y_1984_ = v___y_1994_;
                    v___y_1985_ = v___y_1995_;
                    v___y_1986_ = v___y_1996_;
                    v___y_1987_ = v___y_1999_;
                    v___y_1988_ = v___y_1998_;
                    v___y_1989_ = v___x_2002_;
                    state = 7;
                    continue;
                } else {
                    v_val_2003_ = crate::leanh::lean_ctor_get(v___x_2001_, 0);
                    crate::leanh::lean_inc(v_val_2003_);
                    crate::leanh::lean_dec_ref_known(v___x_2001_, 1);
                    v___y_1982_ = v___y_1993_;
                    v___y_1983_ = v_ref_2000_;
                    v___y_1984_ = v___y_1994_;
                    v___y_1985_ = v___y_1995_;
                    v___y_1986_ = v___y_1996_;
                    v___y_1987_ = v___y_1999_;
                    v___y_1988_ = v___y_1998_;
                    v___y_1989_ = v_val_2003_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2012_ == 0 {
                    v___y_1993_ = v___y_2008_;
                    v___y_1994_ = v___y_2006_;
                    v___y_1995_ = v___y_2007_;
                    v___y_1996_ = v___y_2009_;
                    v___y_1997_ = v___y_2010_;
                    v___y_1998_ = v___y_2011_;
                    v___y_1999_ = v_severity_1915_;
                    state = 8;
                    continue;
                } else {
                    v___y_1993_ = v___y_2008_;
                    v___y_1994_ = v___y_2006_;
                    v___y_1995_ = v___y_2007_;
                    v___y_1996_ = v___y_2009_;
                    v___y_1997_ = v___y_2010_;
                    v___y_1998_ = v___y_2011_;
                    v___y_1999_ = v___x_2004_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2014_ == 0 {
                    v_fileName_2015_ = crate::leanh::lean_ctor_get(v___y_1917_, 0);
                    v_fileMap_2016_ = crate::leanh::lean_ctor_get(v___y_1917_, 1);
                    v_options_2017_ = crate::leanh::lean_ctor_get(v___y_1917_, 2);
                    v_ref_2018_ = crate::leanh::lean_ctor_get(v___y_1917_, 5);
                    v_suppressElabErrors_2019_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1917_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2020_ = crate::leanh::lean_box((v___y_2014_) as usize);
                    v___x_2021_ = crate::leanh::lean_box((v_suppressElabErrors_2019_) as usize);
                    v___f_2022_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2022_, 0, v___x_2020_);
                    crate::leanh::lean_closure_set(v___f_2022_, 1, v___x_2021_);
                    v___x_2023_ = 1;
                    v___x_2024_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1915_, v___x_2023_);
                    if v___x_2024_ == 0 {
                        v___y_2006_ = v_fileMap_2016_;
                        v___y_2007_ = v_suppressElabErrors_2019_;
                        v___y_2008_ = v___f_2022_;
                        v___y_2009_ = v_fileName_2015_;
                        v___y_2010_ = v_ref_2018_;
                        v___y_2011_ = v___y_2014_;
                        v___y_2012_ = v___x_2024_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2025_ = l_Lean_warningAsError;
                        v___x_2026_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_options_2017_, v___x_2025_);
                        v___y_2006_ = v_fileMap_2016_;
                        v___y_2007_ = v_suppressElabErrors_2019_;
                        v___y_2008_ = v___f_2022_;
                        v___y_2009_ = v_fileName_2015_;
                        v___y_2010_ = v_ref_2018_;
                        v___y_2011_ = v___y_2014_;
                        v___y_2012_ = v___x_2026_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1914_);
                    v___x_2027_ = crate::leanh::lean_box(0);
                    v___x_2028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
                    return v___x_2028_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(
    mut v_ref_2031_: *mut crate::leanh::LeanObject,
    mut v_msgData_2032_: *mut crate::leanh::LeanObject,
    mut v_severity_2033_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2038_: u8 = 0;
    let mut v_isSilent_boxed_2039_: u8 = 0;
    let mut v_res_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2038_ = (crate::leanh::lean_unbox(v_severity_2033_) as u8);
    v_isSilent_boxed_2039_ = (crate::leanh::lean_unbox(v_isSilent_2034_) as u8);
    v_res_2040_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_2031_, v_msgData_2032_, v_severity_boxed_2038_, v_isSilent_boxed_2039_, v___y_2035_, v___y_2036_);
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    crate::leanh::lean_dec(v_ref_2031_);
    return v_res_2040_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(
    mut v_ref_2041_: *mut crate::leanh::LeanObject,
    mut v_msgData_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = 1;
    v___x_2047_ = 0;
    v___x_2048_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_2041_, v_msgData_2042_, v___x_2046_, v___x_2047_, v___y_2043_, v___y_2044_);
    return v___x_2048_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(
    mut v_ref_2049_: *mut crate::leanh::LeanObject,
    mut v_msgData_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_2049_, v_msgData_2050_, v___y_2051_, v___y_2052_);
    crate::leanh::lean_dec(v___y_2052_);
    crate::leanh::lean_dec_ref(v___y_2051_);
    crate::leanh::lean_dec(v_ref_2049_);
    return v_res_2054_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0;
    v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2;
    v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
    return v___x_2060_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(
    mut v_linterOption_2061_: *mut crate::leanh::LeanObject,
    mut v_stx_2062_: *mut crate::leanh::LeanObject,
    mut v_msg_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2067_ = crate::leanh::lean_ctor_get(v_linterOption_2061_, 0);
                v_isSharedCheck_2084_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_2061_)) as u8;
                if v_isSharedCheck_2084_ == 0 {
                    v_unused_2085_ = crate::leanh::lean_ctor_get(v_linterOption_2061_, 1);
                    crate::leanh::lean_dec(v_unused_2085_);
                    v___x_2069_ = v_linterOption_2061_;
                    v_isShared_2070_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2067_);
                    crate::leanh::lean_dec(v_linterOption_2061_);
                    v___x_2069_ = crate::leanh::lean_box(0);
                    v_isShared_2070_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2071_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
                crate::leanh::lean_inc(v_name_2067_);
                v___x_2072_ = l_Lean_MessageData_ofName(v_name_2067_);
                if v_isShared_2070_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2069_, 7);
                    crate::leanh::lean_ctor_set(v___x_2069_, 1, v___x_2072_);
                    crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2071_);
                    v___x_2074_ = v___x_2069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2072_);
                    v___x_2074_ = v_reuseFailAlloc_2083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
                v___x_2076_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2076_, 0, v___x_2074_);
                crate::leanh::lean_ctor_set(v___x_2076_, 1, v___x_2075_);
                v_disable_2077_ = l_Lean_MessageData_note(v___x_2076_);
                v___x_2078_ = l_Lean_Linter_linterMessageTag;
                v___x_2079_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2079_, 0, v_msg_2063_);
                crate::leanh::lean_ctor_set(v___x_2079_, 1, v_disable_2077_);
                v___x_2080_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2080_, 0, v___x_2078_);
                crate::leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                v___x_2081_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2081_, 0, v_name_2067_);
                crate::leanh::lean_ctor_set(v___x_2081_, 1, v___x_2080_);
                v___x_2082_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_2062_, v___x_2081_, v___y_2064_, v___y_2065_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(
    mut v_linterOption_2086_: *mut crate::leanh::LeanObject,
    mut v_stx_2087_: *mut crate::leanh::LeanObject,
    mut v_msg_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
    mut v___y_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_2086_, v_stx_2087_, v_msg_2088_, v___y_2089_, v___y_2090_);
    crate::leanh::lean_dec(v___y_2090_);
    crate::leanh::lean_dec_ref(v___y_2089_);
    crate::leanh::lean_dec(v_stx_2087_);
    return v_res_2092_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4;
    v___x_2102_ = l_Lean_MessageData_ofFormat(v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6;
    v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12;
    v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
    return v___x_2116_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once
        ),
        _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13,
    );
    v___x_2118_ = l_Lean_MessageData_note(v___x_2117_);
    return v___x_2118_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15;
    v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
    return v___x_2121_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17;
    v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(
    mut v_stx_2125_: *mut crate::leanh::LeanObject,
    mut v_i_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hint_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpArgs_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_argStx_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_otherArgs_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_a_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = crate::leanh::lean_box(0);
                v___x_2140_ =
                    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1;
                v_simpArgs_2141_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_2125_);
                v___x_2192_ = lean_array_get_size(v_simpArgs_2141_);
                v___x_2193_ = lean_nat_dec_lt(v_i_2126_, v___x_2192_);
                if v___x_2193_ == 0 {
                    crate::leanh::lean_dec_ref(v_simpArgs_2141_);
                    v___x_2194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
                    v___x_2195_ = l_Nat_reprFast(v_i_2126_);
                    v___x_2196_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2195_);
                    v___x_2197_ = l_Lean_MessageData_ofFormat(v___x_2196_);
                    v___x_2198_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2194_);
                    crate::leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
                    v___x_2199_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
                    v___x_2200_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2198_);
                    crate::leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                    v___x_2201_ = l_Lean_MessageData_ofSyntax(v_stx_2125_);
                    v___x_2202_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2202_, 0, v___x_2200_);
                    crate::leanh::lean_ctor_set(v___x_2202_, 1, v___x_2201_);
                    v___x_2203_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_2202_, v_a_2127_, v_a_2128_);
                    return v___x_2203_;
                } else {
                    v___y_2143_ = v_a_2127_;
                    v___y_2144_ = v_a_2128_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2136_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
                v___x_2137_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2137_, 0, v___y_2131_);
                crate::leanh::lean_ctor_set(v___x_2137_, 1, v_hint_2133_);
                v___x_2138_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_2136_, v___y_2132_, v___x_2137_, v___y_2134_, v___y_2135_);
                crate::leanh::lean_dec(v___y_2132_);
                return v___x_2138_;
            }
            2 => {
                v___x_2145_ = lean_array_get_size(v_simpArgs_2141_);
                v___x_2146_ = crate::leanh::lean_unsigned_to_nat(0);
                v_argStx_2147_ = lean_array_get(v___x_2139_, v_simpArgs_2141_, v_i_2126_);
                v_otherArgs_2148_ =
                    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2;
                v___x_2149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_2145_, v_i_2126_, v_simpArgs_2141_, v___x_2146_, v_otherArgs_2148_);
                crate::leanh::lean_dec_ref(v_simpArgs_2141_);
                crate::leanh::lean_dec(v_i_2126_);
                if crate::leanh::lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    crate::leanh::lean_inc(v_a_2150_);
                    crate::leanh::lean_dec_ref_known(v___x_2149_, 1);
                    crate::leanh::lean_inc(v_stx_2125_);
                    v___x_2151_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_2125_, v_a_2150_);
                    crate::leanh::lean_dec(v_a_2150_);
                    v___x_2152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2140_);
                    crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                    v___x_2153_ = crate::leanh::lean_box(0);
                    v___x_2154_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2152_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 2, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 3, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 4, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 5, v___x_2153_);
                    v___x_2155_ = 0;
                    v___x_2156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2156_, 0, v_stx_2125_);
                    v___x_2157_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2154_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 2, v___x_2153_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_2155_,
                    );
                    v___x_2158_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5);
                    v___x_2159_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2160_ = lean_mk_empty_array_with_capacity(v___x_2159_);
                    v___x_2161_ = lean_array_push(v___x_2160_, v___x_2157_);
                    v___x_2162_ = 0;
                    v___x_2163_ = l_Lean_MessageData_hint(
                        v___x_2158_,
                        v___x_2161_,
                        v___x_2153_,
                        v___x_2153_,
                        v___x_2162_,
                        v___y_2143_,
                        v___y_2144_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2161_);
                    if crate::leanh::lean_obj_tag(v___x_2163_) == 0 {
                        v_a_2164_ = crate::leanh::lean_ctor_get(v___x_2163_, 0);
                        crate::leanh::lean_inc(v_a_2164_);
                        crate::leanh::lean_dec_ref_known(v___x_2163_, 1);
                        v___x_2165_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
                        crate::leanh::lean_inc_n(v_argStx_2147_, 2);
                        v___x_2166_ = l_Lean_MessageData_ofSyntax(v_argStx_2147_);
                        v___x_2167_ = l_Lean_indentD(v___x_2166_);
                        v_msg_2168_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_msg_2168_, 0, v___x_2165_);
                        crate::leanh::lean_ctor_set(v_msg_2168_, 1, v___x_2167_);
                        v___x_2169_ = l_Lean_Syntax_getKind(v_argStx_2147_);
                        v___x_2170_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11;
                        v___x_2171_ = lean_name_eq(v___x_2169_, v___x_2170_);
                        crate::leanh::lean_dec(v___x_2169_);
                        if v___x_2171_ == 0 {
                            v___y_2131_ = v_msg_2168_;
                            v___y_2132_ = v_argStx_2147_;
                            v_hint_2133_ = v_a_2164_;
                            v___y_2134_ = v___y_2143_;
                            v___y_2135_ = v___y_2144_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2172_ = l_Lean_Syntax_getArg(v_argStx_2147_, v___x_2159_);
                            v___x_2173_ = l_Lean_Syntax_isNone(v___x_2172_);
                            crate::leanh::lean_dec(v___x_2172_);
                            if v___x_2173_ == 0 {
                                if v___x_2171_ == 0 {
                                    v___y_2131_ = v_msg_2168_;
                                    v___y_2132_ = v_argStx_2147_;
                                    v_hint_2133_ = v_a_2164_;
                                    v___y_2134_ = v___y_2143_;
                                    v___y_2135_ = v___y_2144_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2174_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
                                    v___x_2175_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2175_, 0, v_a_2164_);
                                    crate::leanh::lean_ctor_set(v___x_2175_, 1, v___x_2174_);
                                    v___y_2131_ = v_msg_2168_;
                                    v___y_2132_ = v_argStx_2147_;
                                    v_hint_2133_ = v___x_2175_;
                                    v___y_2134_ = v___y_2143_;
                                    v___y_2135_ = v___y_2144_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_2131_ = v_msg_2168_;
                                v___y_2132_ = v_argStx_2147_;
                                v_hint_2133_ = v_a_2164_;
                                v___y_2134_ = v___y_2143_;
                                v___y_2135_ = v___y_2144_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_argStx_2147_);
                        v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2163_, 0);
                        v_isSharedCheck_2183_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2163_)) as u8;
                        if v_isSharedCheck_2183_ == 0 {
                            v___x_2178_ = v___x_2163_;
                            v_isShared_2179_ = v_isSharedCheck_2183_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2176_);
                            crate::leanh::lean_dec(v___x_2163_);
                            v___x_2178_ = crate::leanh::lean_box(0);
                            v_isShared_2179_ = v_isSharedCheck_2183_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_argStx_2147_);
                    crate::leanh::lean_dec(v_stx_2125_);
                    v_a_2184_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2191_ = (!crate::leanh::lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2186_ = v___x_2149_;
                        v_isShared_2187_ = v_isSharedCheck_2191_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2184_);
                        crate::leanh::lean_dec(v___x_2149_);
                        v___x_2186_ = crate::leanh::lean_box(0);
                        v_isShared_2187_ = v_isSharedCheck_2191_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2179_ == 0 {
                    v___x_2181_ = v___x_2178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
                    v___x_2181_ = v_reuseFailAlloc_2182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2181_;
            }
            5 => {
                if v_isShared_2187_ == 0 {
                    v___x_2189_ = v___x_2186_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
                    v___x_2189_ = v_reuseFailAlloc_2190_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(
    mut v_stx_2204_: *mut crate::leanh::LeanObject,
    mut v_i_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2209_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(
        v_stx_2204_,
        v_i_2205_,
        v_a_2206_,
        v_a_2207_,
    );
    crate::leanh::lean_dec(v_a_2207_);
    crate::leanh::lean_dec_ref(v_a_2206_);
    return v_res_2209_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(
    mut v_upperBound_2210_: *mut crate::leanh::LeanObject,
    mut v_i_2211_: *mut crate::leanh::LeanObject,
    mut v_simpArgs_2212_: *mut crate::leanh::LeanObject,
    mut v_inst_2213_: *mut crate::leanh::LeanObject,
    mut v_R_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_b_2216_: *mut crate::leanh::LeanObject,
    mut v_c_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_2210_, v_i_2211_, v_simpArgs_2212_, v_a_2215_, v_b_2216_);
    return v___x_2221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(
    mut v_upperBound_2222_: *mut crate::leanh::LeanObject,
    mut v_i_2223_: *mut crate::leanh::LeanObject,
    mut v_simpArgs_2224_: *mut crate::leanh::LeanObject,
    mut v_inst_2225_: *mut crate::leanh::LeanObject,
    mut v_R_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_b_2228_: *mut crate::leanh::LeanObject,
    mut v_c_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_2222_, v_i_2223_, v_simpArgs_2224_, v_inst_2225_, v_R_2226_, v_a_2227_, v_b_2228_, v_c_2229_, v___y_2230_, v___y_2231_);
    crate::leanh::lean_dec(v___y_2231_);
    crate::leanh::lean_dec_ref(v___y_2230_);
    crate::leanh::lean_dec_ref(v_simpArgs_2224_);
    crate::leanh::lean_dec(v_i_2223_);
    crate::leanh::lean_dec(v_upperBound_2222_);
    return v_res_2233_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(
    mut v_00_u03b1_2234_: *mut crate::leanh::LeanObject,
    mut v_msg_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_2235_, v___y_2236_, v___y_2237_);
    return v___x_2239_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(
    mut v_00_u03b1_2240_: *mut crate::leanh::LeanObject,
    mut v_msg_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2245_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_2240_, v_msg_2241_, v___y_2242_, v___y_2243_);
    crate::leanh::lean_dec(v___y_2243_);
    crate::leanh::lean_dec_ref(v___y_2242_);
    return v_res_2245_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(
    mut v_upperBound_2246_: *mut crate::leanh::LeanObject,
    mut v_snd_2247_: *mut crate::leanh::LeanObject,
    mut v_fst_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_b_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2259_ = lean_nat_dec_lt(v_a_2249_, v_upperBound_2246_);
                if v___x_2259_ == 0 {
                    crate::leanh::lean_dec(v_a_2249_);
                    crate::leanh::lean_dec(v_fst_2248_);
                    v___x_2260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2260_, 0, v_b_2250_);
                    return v___x_2260_;
                } else {
                    v___x_2261_ = crate::leanh::lean_box(0);
                    v___x_2262_ = 0;
                    v___x_2263_ = crate::leanh::lean_box((v___x_2262_) as usize);
                    v___x_2264_ = lean_array_get(v___x_2263_, v_snd_2247_, v_a_2249_);
                    crate::leanh::lean_dec(v___x_2263_);
                    v___x_2265_ = (crate::leanh::lean_unbox(v___x_2264_) as u8);
                    crate::leanh::lean_dec(v___x_2264_);
                    if v___x_2265_ == 0 {
                        crate::leanh::lean_inc(v_a_2249_);
                        crate::leanh::lean_inc(v_fst_2248_);
                        v___x_2266_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed
                                as *mut core::ffi::c_void,
                            5,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_2266_, 0, v_fst_2248_);
                        crate::leanh::lean_closure_set(v___x_2266_, 1, v_a_2249_);
                        v___x_2267_ = l_Lean_Elab_Command_liftCoreM___redArg(
                            v___x_2266_,
                            v___y_2251_,
                            v___y_2252_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2267_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2267_, 1);
                            v_a_2255_ = v___x_2261_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2249_);
                            crate::leanh::lean_dec(v_fst_2248_);
                            return v___x_2267_;
                        }
                    } else {
                        v_a_2255_ = v___x_2261_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2256_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2257_ = lean_nat_add(v_a_2249_, v___x_2256_);
                crate::leanh::lean_dec(v_a_2249_);
                v_a_2249_ = v___x_2257_;
                v_b_2250_ = v_a_2255_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(
    mut v_upperBound_2268_: *mut crate::leanh::LeanObject,
    mut v_snd_2269_: *mut crate::leanh::LeanObject,
    mut v_fst_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_b_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(
            v_upperBound_2268_,
            v_snd_2269_,
            v_fst_2270_,
            v_a_2271_,
            v_b_2272_,
            v___y_2273_,
            v___y_2274_,
        );
    crate::leanh::lean_dec(v___y_2274_);
    crate::leanh::lean_dec_ref(v___y_2273_);
    crate::leanh::lean_dec_ref(v_snd_2269_);
    crate::leanh::lean_dec(v_upperBound_2268_);
    return v_res_2276_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(
    mut v_as_2277_: *mut crate::leanh::LeanObject,
    mut v_sz_2278_: usize,
    mut v_i_2279_: usize,
    mut v_b_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2284_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
                if v___x_2284_ == 0 {
                    v___x_2285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2285_, 0, v_b_2280_);
                    return v___x_2285_;
                } else {
                    v_a_2286_ = lean_array_uget_borrowed(v_as_2277_, v_i_2279_);
                    v_snd_2287_ = crate::leanh::lean_ctor_get(v_a_2286_, 1);
                    v_fst_2288_ = crate::leanh::lean_ctor_get(v_snd_2287_, 0);
                    v_snd_2289_ = crate::leanh::lean_ctor_get(v_snd_2287_, 1);
                    v___x_2290_ = crate::leanh::lean_box(0);
                    v___x_2291_ = lean_array_get_size(v_snd_2289_);
                    v___x_2292_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_fst_2288_);
                    v___x_2293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_2291_, v_snd_2289_, v_fst_2288_, v___x_2292_, v___x_2290_, v___y_2281_, v___y_2282_);
                    if crate::leanh::lean_obj_tag(v___x_2293_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2293_, 1);
                        v___x_2294_ = 1usize;
                        v___x_2295_ = lean_usize_add(v_i_2279_, v___x_2294_);
                        v_i_2279_ = v___x_2295_;
                        v_b_2280_ = v___x_2290_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2293_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(
    mut v_as_2297_: *mut crate::leanh::LeanObject,
    mut v_sz_2298_: *mut crate::leanh::LeanObject,
    mut v_i_2299_: *mut crate::leanh::LeanObject,
    mut v_b_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2304_: usize = 0;
    let mut v_i_boxed_2305_: usize = 0;
    let mut v_res_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2304_ = crate::leanh::lean_unbox_usize(v_sz_2298_);
    crate::leanh::lean_dec(v_sz_2298_);
    v_i_boxed_2305_ = crate::leanh::lean_unbox_usize(v_i_2299_);
    crate::leanh::lean_dec(v_i_2299_);
    v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_2297_, v_sz_boxed_2304_, v_i_boxed_2305_, v_b_2300_, v___y_2301_, v___y_2302_);
    crate::leanh::lean_dec(v___y_2302_);
    crate::leanh::lean_dec_ref(v___y_2301_);
    crate::leanh::lean_dec_ref(v_as_2297_);
    return v_res_2306_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(
    mut v_hi_2307_: *mut crate::leanh::LeanObject,
    mut v_pivot_2308_: *mut crate::leanh::LeanObject,
    mut v_as_2309_: *mut crate::leanh::LeanObject,
    mut v_i_2310_: *mut crate::leanh::LeanObject,
    mut v_k_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2312_ = lean_nat_dec_lt(v_k_2311_, v_hi_2307_);
                if v___x_2312_ == 0 {
                    crate::leanh::lean_dec(v_k_2311_);
                    v___x_2313_ = lean_array_fswap(v_as_2309_, v_i_2310_, v_hi_2307_);
                    v___x_2314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2314_, 0, v_i_2310_);
                    crate::leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
                    return v___x_2314_;
                } else {
                    v___x_2315_ = lean_array_fget_borrowed(v_as_2309_, v_k_2311_);
                    v_fst_2316_ = crate::leanh::lean_ctor_get(v___x_2315_, 0);
                    v_fst_2317_ = crate::leanh::lean_ctor_get(v_pivot_2308_, 0);
                    v_start_2318_ = crate::leanh::lean_ctor_get(v_fst_2316_, 0);
                    v_start_2319_ = crate::leanh::lean_ctor_get(v_fst_2317_, 0);
                    v___x_2320_ = lean_nat_dec_lt(v_start_2318_, v_start_2319_);
                    if v___x_2320_ == 0 {
                        v___x_2321_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2322_ = lean_nat_add(v_k_2311_, v___x_2321_);
                        crate::leanh::lean_dec(v_k_2311_);
                        v_k_2311_ = v___x_2322_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2324_ = lean_array_fswap(v_as_2309_, v_i_2310_, v_k_2311_);
                        v___x_2325_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2326_ = lean_nat_add(v_i_2310_, v___x_2325_);
                        crate::leanh::lean_dec(v_i_2310_);
                        v___x_2327_ = lean_nat_add(v_k_2311_, v___x_2325_);
                        crate::leanh::lean_dec(v_k_2311_);
                        v_as_2309_ = v___x_2324_;
                        v_i_2310_ = v___x_2326_;
                        v_k_2311_ = v___x_2327_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(
    mut v_hi_2329_: *mut crate::leanh::LeanObject,
    mut v_pivot_2330_: *mut crate::leanh::LeanObject,
    mut v_as_2331_: *mut crate::leanh::LeanObject,
    mut v_i_2332_: *mut crate::leanh::LeanObject,
    mut v_k_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_2329_, v_pivot_2330_, v_as_2331_, v_i_2332_, v_k_2333_);
    crate::leanh::lean_dec_ref(v_pivot_2330_);
    crate::leanh::lean_dec(v_hi_2329_);
    return v_res_2334_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(
    mut v_x1_2335_: *mut crate::leanh::LeanObject,
    mut v_x2_2336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: u8 = 0;
    v_fst_2337_ = crate::leanh::lean_ctor_get(v_x1_2335_, 0);
    v_fst_2338_ = crate::leanh::lean_ctor_get(v_x2_2336_, 0);
    v_start_2339_ = crate::leanh::lean_ctor_get(v_fst_2337_, 0);
    v_start_2340_ = crate::leanh::lean_ctor_get(v_fst_2338_, 0);
    v___x_2341_ = lean_nat_dec_lt(v_start_2339_, v_start_2340_);
    return v___x_2341_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(
    mut v_x1_2342_: *mut crate::leanh::LeanObject,
    mut v_x2_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2344_: u8 = 0;
    let mut v_r_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_2342_, v_x2_2343_);
    crate::leanh::lean_dec_ref(v_x2_2343_);
    crate::leanh::lean_dec_ref(v_x1_2342_);
    v_r_2345_ = crate::leanh::lean_box((v_res_2344_) as usize);
    return v_r_2345_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(
    mut v_n_2346_: *mut crate::leanh::LeanObject,
    mut v_as_2347_: *mut crate::leanh::LeanObject,
    mut v_lo_2348_: *mut crate::leanh::LeanObject,
    mut v_hi_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2361_ = lean_nat_dec_lt(v_lo_2348_, v_hi_2349_);
                if v___x_2361_ == 0 {
                    crate::leanh::lean_dec(v_lo_2348_);
                    return v_as_2347_;
                } else {
                    v___x_2362_ = lean_nat_add(v_lo_2348_, v_hi_2349_);
                    v___x_2363_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_2364_ = lean_nat_shiftr(v___x_2362_, v___x_2363_);
                    crate::leanh::lean_dec(v___x_2362_);
                    v___x_2377_ = lean_array_fget_borrowed(v_as_2347_, v_mid_2364_);
                    v___x_2378_ = lean_array_fget_borrowed(v_as_2347_, v_lo_2348_);
                    v___x_2379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_2377_, v___x_2378_);
                    if v___x_2379_ == 0 {
                        v___y_2372_ = v_as_2347_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2380_ = lean_array_fswap(v_as_2347_, v_lo_2348_, v_mid_2364_);
                        v___y_2372_ = v___x_2380_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2352_ = lean_array_fget(v___y_2351_, v_hi_2349_);
                crate::leanh::lean_inc_n(v_lo_2348_, 2);
                v___x_2353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_2349_, v_pivot_2352_, v___y_2351_, v_lo_2348_, v_lo_2348_);
                crate::leanh::lean_dec(v_pivot_2352_);
                v_fst_2354_ = crate::leanh::lean_ctor_get(v___x_2353_, 0);
                crate::leanh::lean_inc(v_fst_2354_);
                v_snd_2355_ = crate::leanh::lean_ctor_get(v___x_2353_, 1);
                crate::leanh::lean_inc(v_snd_2355_);
                crate::leanh::lean_dec_ref(v___x_2353_);
                v___x_2356_ = lean_nat_dec_le(v_hi_2349_, v_fst_2354_);
                if v___x_2356_ == 0 {
                    v___x_2357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_2346_, v_snd_2355_, v_lo_2348_, v_fst_2354_);
                    v___x_2358_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2359_ = lean_nat_add(v_fst_2354_, v___x_2358_);
                    crate::leanh::lean_dec(v_fst_2354_);
                    v_as_2347_ = v___x_2357_;
                    v_lo_2348_ = v___x_2359_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2354_);
                    crate::leanh::lean_dec(v_lo_2348_);
                    return v_snd_2355_;
                }
            }
            2 => {
                v___x_2367_ = lean_array_fget_borrowed(v___y_2366_, v_mid_2364_);
                v___x_2368_ = lean_array_fget_borrowed(v___y_2366_, v_hi_2349_);
                v___x_2369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_2367_, v___x_2368_);
                if v___x_2369_ == 0 {
                    crate::leanh::lean_dec(v_mid_2364_);
                    v___y_2351_ = v___y_2366_;
                    state = 1;
                    continue;
                } else {
                    v___x_2370_ = lean_array_fswap(v___y_2366_, v_mid_2364_, v_hi_2349_);
                    crate::leanh::lean_dec(v_mid_2364_);
                    v___y_2351_ = v___x_2370_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2373_ = lean_array_fget_borrowed(v___y_2372_, v_hi_2349_);
                v___x_2374_ = lean_array_fget_borrowed(v___y_2372_, v_lo_2348_);
                v___x_2375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_2373_, v___x_2374_);
                if v___x_2375_ == 0 {
                    v___y_2366_ = v___y_2372_;
                    state = 2;
                    continue;
                } else {
                    v___x_2376_ = lean_array_fswap(v___y_2372_, v_lo_2348_, v_hi_2349_);
                    v___y_2366_ = v___x_2376_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(
    mut v_n_2381_: *mut crate::leanh::LeanObject,
    mut v_as_2382_: *mut crate::leanh::LeanObject,
    mut v_lo_2383_: *mut crate::leanh::LeanObject,
    mut v_hi_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_2381_, v_as_2382_, v_lo_2383_, v_hi_2384_);
    crate::leanh::lean_dec(v_hi_2384_);
    crate::leanh::lean_dec(v_n_2381_);
    return v_res_2385_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(
    mut v_x_2386_: *mut crate::leanh::LeanObject,
    mut v_x_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2387_) == 0 {
                    return v_x_2386_;
                } else {
                    v_key_2388_ = crate::leanh::lean_ctor_get(v_x_2387_, 0);
                    v_value_2389_ = crate::leanh::lean_ctor_get(v_x_2387_, 1);
                    v_tail_2390_ = crate::leanh::lean_ctor_get(v_x_2387_, 2);
                    crate::leanh::lean_inc(v_value_2389_);
                    crate::leanh::lean_inc(v_key_2388_);
                    v___x_2391_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2391_, 0, v_key_2388_);
                    crate::leanh::lean_ctor_set(v___x_2391_, 1, v_value_2389_);
                    v___x_2392_ = lean_array_push(v_x_2386_, v___x_2391_);
                    v_x_2386_ = v___x_2392_;
                    v_x_2387_ = v_tail_2390_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(
    mut v_x_2394_: *mut crate::leanh::LeanObject,
    mut v_x_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(
            v_x_2394_, v_x_2395_,
        );
    crate::leanh::lean_dec(v_x_2395_);
    return v_res_2396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(
    mut v_as_2397_: *mut crate::leanh::LeanObject,
    mut v_i_2398_: usize,
    mut v_stop_2399_: usize,
    mut v_b_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2401_ = lean_usize_dec_eq(v_i_2398_, v_stop_2399_);
                if v___x_2401_ == 0 {
                    v___x_2402_ = lean_array_uget_borrowed(v_as_2397_, v_i_2398_);
                    v___x_2403_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_b_2400_, v___x_2402_);
                    v___x_2404_ = 1usize;
                    v___x_2405_ = lean_usize_add(v_i_2398_, v___x_2404_);
                    v_i_2398_ = v___x_2405_;
                    v_b_2400_ = v___x_2403_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2400_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(
    mut v_as_2407_: *mut crate::leanh::LeanObject,
    mut v_i_2408_: *mut crate::leanh::LeanObject,
    mut v_stop_2409_: *mut crate::leanh::LeanObject,
    mut v_b_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2411_: usize = 0;
    let mut v_stop_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2411_ = crate::leanh::lean_unbox_usize(v_i_2408_);
    crate::leanh::lean_dec(v_i_2408_);
    v_stop_boxed_2412_ = crate::leanh::lean_unbox_usize(v_stop_2409_);
    crate::leanh::lean_dec(v_stop_2409_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_2407_, v_i_boxed_2411_, v_stop_boxed_2412_, v_b_2410_);
    crate::leanh::lean_dec_ref(v_as_2407_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(
    mut v_o_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2417_ = lean_st_ref_get(v___y_2415_);
    v_env_2418_ = crate::leanh::lean_ctor_get(v___x_2417_, 0);
    crate::leanh::lean_inc_ref(v_env_2418_);
    crate::leanh::lean_dec(v___x_2417_);
    v___x_2419_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2420_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
    v_asyncMode_2421_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2420_, 2);
    v___x_2422_ = crate::leanh::lean_box(1);
    v___x_2423_ = crate::leanh::lean_box(0);
    v_linterSets_2424_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2422_,
        v___x_2419_,
        v_env_2418_,
        v_asyncMode_2421_,
        v___x_2423_,
    );
    v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2425_, 0, v_o_2414_);
    crate::leanh::lean_ctor_set(v___x_2425_, 1, v_linterSets_2424_);
    v___x_2426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2425_);
    return v___x_2426_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(
    mut v_o_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_2427_, v___y_2428_);
    crate::leanh::lean_dec(v___y_2428_);
    return v_res_2430_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = lean_st_ref_get(v___y_2432_);
    v_scopes_2435_ = crate::leanh::lean_ctor_get(v___x_2434_, 2);
    crate::leanh::lean_inc(v_scopes_2435_);
    crate::leanh::lean_dec(v___x_2434_);
    v___x_2436_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2437_ = l_List_head_x21___redArg(v___x_2436_, v_scopes_2435_);
    crate::leanh::lean_dec(v_scopes_2435_);
    v_opts_2438_ = crate::leanh::lean_ctor_get(v___x_2437_, 1);
    crate::leanh::lean_inc_ref(v_opts_2438_);
    crate::leanh::lean_dec(v___x_2437_);
    v___x_2439_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_2438_, v___y_2432_);
    return v___x_2439_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(
        v___y_2440_,
        v___y_2441_,
    );
    crate::leanh::lean_dec(v___y_2441_);
    crate::leanh::lean_dec_ref(v___y_2440_);
    return v_res_2443_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_x_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2445_) == 0 {
                    v___x_2446_ = crate::leanh::lean_box(0);
                    return v___x_2446_;
                } else {
                    v_key_2447_ = crate::leanh::lean_ctor_get(v_x_2445_, 0);
                    v_value_2448_ = crate::leanh::lean_ctor_get(v_x_2445_, 1);
                    v_tail_2449_ = crate::leanh::lean_ctor_get(v_x_2445_, 2);
                    v___x_2450_ = l_Lean_Syntax_instBEqRange_beq(v_key_2447_, v_a_2444_);
                    if v___x_2450_ == 0 {
                        v_x_2445_ = v_tail_2449_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2448_);
                        v___x_2452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2452_, 0, v_value_2448_);
                        return v___x_2452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_x_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_2453_, v_x_2454_);
    crate::leanh::lean_dec(v_x_2454_);
    crate::leanh::lean_dec_ref(v_a_2453_);
    return v_res_2455_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(
    mut v_m_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u64 = 0;
    let mut v___x_2461_: u64 = 0;
    let mut v___x_2462_: u64 = 0;
    let mut v_fold_2463_: u64 = 0;
    let mut v___x_2464_: u64 = 0;
    let mut v___x_2465_: u64 = 0;
    let mut v___x_2466_: u64 = 0;
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: usize = 0;
    let mut v___x_2469_: usize = 0;
    let mut v___x_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2458_ = crate::leanh::lean_ctor_get(v_m_2456_, 1);
    v___x_2459_ = lean_array_get_size(v_buckets_2458_);
    v___x_2460_ = l_Lean_Syntax_instHashableRange_hash(v_a_2457_);
    v___x_2461_ = 32u64;
    v___x_2462_ = lean_uint64_shift_right(v___x_2460_, v___x_2461_);
    v_fold_2463_ = lean_uint64_xor(v___x_2460_, v___x_2462_);
    v___x_2464_ = 16u64;
    v___x_2465_ = lean_uint64_shift_right(v_fold_2463_, v___x_2464_);
    v___x_2466_ = lean_uint64_xor(v_fold_2463_, v___x_2465_);
    v___x_2467_ = lean_uint64_to_usize(v___x_2466_);
    v___x_2468_ = lean_usize_of_nat(v___x_2459_);
    v___x_2469_ = 1usize;
    v___x_2470_ = lean_usize_sub(v___x_2468_, v___x_2469_);
    v___x_2471_ = lean_usize_land(v___x_2467_, v___x_2470_);
    v___x_2472_ = lean_array_uget_borrowed(v_buckets_2458_, v___x_2471_);
    v___x_2473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_2457_, v___x_2472_);
    return v___x_2473_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(
    mut v_m_2474_: *mut crate::leanh::LeanObject,
    mut v_a_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_2474_, v_a_2475_);
    crate::leanh::lean_dec_ref(v_a_2475_);
    crate::leanh::lean_dec_ref(v_m_2474_);
    return v_res_2476_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
    mut v___x_2477_: u8,
    mut v_as_2478_: *mut crate::leanh::LeanObject,
    mut v_bs_2479_: *mut crate::leanh::LeanObject,
    mut v_i_2480_: *mut crate::leanh::LeanObject,
    mut v_cs_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2483_: u8 = 0;
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v_b_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2489_ = lean_array_get_size(v_as_2478_);
                v___x_2490_ = lean_nat_dec_lt(v_i_2480_, v___x_2489_);
                if v___x_2490_ == 0 {
                    crate::leanh::lean_dec(v_i_2480_);
                    return v_cs_2481_;
                } else {
                    v___x_2491_ = lean_array_get_size(v_bs_2479_);
                    v___x_2492_ = lean_nat_dec_lt(v_i_2480_, v___x_2491_);
                    if v___x_2492_ == 0 {
                        crate::leanh::lean_dec(v_i_2480_);
                        return v_cs_2481_;
                    } else {
                        v_a_2493_ = lean_array_fget_borrowed(v_as_2478_, v_i_2480_);
                        v___x_2494_ = (crate::leanh::lean_unbox(v_a_2493_) as u8);
                        if v___x_2494_ == 0 {
                            v_b_2495_ = lean_array_fget_borrowed(v_bs_2479_, v_i_2480_);
                            v___x_2496_ = (crate::leanh::lean_unbox(v_b_2495_) as u8);
                            v___y_2483_ = v___x_2496_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2483_ = v___x_2477_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2484_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2485_ = lean_nat_add(v_i_2480_, v___x_2484_);
                crate::leanh::lean_dec(v_i_2480_);
                v___x_2486_ = crate::leanh::lean_box((v___y_2483_) as usize);
                v___x_2487_ = lean_array_push(v_cs_2481_, v___x_2486_);
                v_i_2480_ = v___x_2485_;
                v_cs_2481_ = v___x_2487_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(
    mut v___x_2497_: *mut crate::leanh::LeanObject,
    mut v_as_2498_: *mut crate::leanh::LeanObject,
    mut v_bs_2499_: *mut crate::leanh::LeanObject,
    mut v_i_2500_: *mut crate::leanh::LeanObject,
    mut v_cs_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14147__boxed_2502_: u8 = 0;
    let mut v_res_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14147__boxed_2502_ = (crate::leanh::lean_unbox(v___x_2497_) as u8);
    v_res_2503_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
        v___x_14147__boxed_2502_,
        v_as_2498_,
        v_bs_2499_,
        v_i_2500_,
        v_cs_2501_,
    );
    crate::leanh::lean_dec_ref(v_bs_2499_);
    crate::leanh::lean_dec_ref(v_as_2498_);
    return v_res_2503_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(
    mut v_msgData_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = lean_st_ref_get(v___y_2505_);
    v_env_2508_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
    crate::leanh::lean_inc_ref(v_env_2508_);
    crate::leanh::lean_dec(v___x_2507_);
    v___x_2509_ = lean_st_ref_get(v___y_2505_);
    v_scopes_2510_ = crate::leanh::lean_ctor_get(v___x_2509_, 2);
    crate::leanh::lean_inc(v_scopes_2510_);
    crate::leanh::lean_dec(v___x_2509_);
    v___x_2511_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2512_ = l_List_head_x21___redArg(v___x_2511_, v_scopes_2510_);
    crate::leanh::lean_dec(v_scopes_2510_);
    v_opts_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 1);
    crate::leanh::lean_inc_ref(v_opts_2513_);
    crate::leanh::lean_dec(v___x_2512_);
    v___x_2514_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
    v___x_2515_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2516_ = lean_mk_empty_array_with_capacity(v___x_2515_);
    crate::leanh::lean_dec_ref(v___x_2516_);
    v___x_2517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
    v___x_2518_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2518_, 0, v_env_2508_);
    crate::leanh::lean_ctor_set(v___x_2518_, 1, v___x_2514_);
    crate::leanh::lean_ctor_set(v___x_2518_, 2, v___x_2517_);
    crate::leanh::lean_ctor_set(v___x_2518_, 3, v_opts_2513_);
    v___x_2519_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    crate::leanh::lean_ctor_set(v___x_2519_, 1, v_msgData_2504_);
    v___x_2520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(
    mut v_msgData_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_2521_, v___y_2522_);
    crate::leanh::lean_dec(v___y_2522_);
    return v_res_2524_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = crate::leanh::lean_box(1);
    v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
    return v___x_2526_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2;
    v___x_2531_ = l_Lean_MessageData_ofFormat(v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(
    mut v_x_2532_: *mut crate::leanh::LeanObject,
    mut v_x_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v_before_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_unused_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2533_) == 0 {
                    return v_x_2532_;
                } else {
                    v_head_2534_ = crate::leanh::lean_ctor_get(v_x_2533_, 0);
                    v_tail_2535_ = crate::leanh::lean_ctor_get(v_x_2533_, 1);
                    v_isSharedCheck_2557_ = (!crate::leanh::lean_is_exclusive(v_x_2533_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v___x_2537_ = v_x_2533_;
                        v_isShared_2538_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2535_);
                        crate::leanh::lean_inc(v_head_2534_);
                        crate::leanh::lean_dec(v_x_2533_);
                        v___x_2537_ = crate::leanh::lean_box(0);
                        v_isShared_2538_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2539_ = crate::leanh::lean_ctor_get(v_head_2534_, 0);
                v_isSharedCheck_2555_ = (!crate::leanh::lean_is_exclusive(v_head_2534_)) as u8;
                if v_isSharedCheck_2555_ == 0 {
                    v_unused_2556_ = crate::leanh::lean_ctor_get(v_head_2534_, 1);
                    crate::leanh::lean_dec(v_unused_2556_);
                    v___x_2541_ = v_head_2534_;
                    v_isShared_2542_ = v_isSharedCheck_2555_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2539_);
                    crate::leanh::lean_dec(v_head_2534_);
                    v___x_2541_ = crate::leanh::lean_box(0);
                    v_isShared_2542_ = v_isSharedCheck_2555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2543_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
                if v_isShared_2542_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2541_, 7);
                    crate::leanh::lean_ctor_set(v___x_2541_, 1, v___x_2543_);
                    crate::leanh::lean_ctor_set(v___x_2541_, 0, v_x_2532_);
                    v___x_2545_ = v___x_2541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_x_2532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2543_);
                    v___x_2545_ = v_reuseFailAlloc_2554_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2546_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
                if v_isShared_2538_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2537_, 7);
                    crate::leanh::lean_ctor_set(v___x_2537_, 1, v___x_2546_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2545_);
                    v___x_2548_ = v___x_2537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2546_);
                    v___x_2548_ = v_reuseFailAlloc_2553_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2549_ = l_Lean_MessageData_ofSyntax(v_before_2539_);
                v___x_2550_ = l_Lean_indentD(v___x_2549_);
                v___x_2551_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2551_, 0, v___x_2548_);
                crate::leanh::lean_ctor_set(v___x_2551_, 1, v___x_2550_);
                v_x_2532_ = v___x_2551_;
                v_x_2533_ = v_tail_2535_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1;
    v___x_2562_ = l_Lean_MessageData_ofFormat(v___x_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(
    mut v_msgData_2563_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v_unused_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2567_ = lean_st_ref_get(v___y_2565_);
                v_scopes_2568_ = crate::leanh::lean_ctor_get(v___x_2567_, 2);
                crate::leanh::lean_inc(v_scopes_2568_);
                crate::leanh::lean_dec(v___x_2567_);
                v___x_2569_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2570_ = l_List_head_x21___redArg(v___x_2569_, v_scopes_2568_);
                crate::leanh::lean_dec(v_scopes_2568_);
                v_opts_2571_ = crate::leanh::lean_ctor_get(v___x_2570_, 1);
                crate::leanh::lean_inc_ref(v_opts_2571_);
                crate::leanh::lean_dec(v___x_2570_);
                v___x_2572_ = l_Lean_Elab_pp_macroStack;
                v___x_2573_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_2571_, v___x_2572_);
                crate::leanh::lean_dec_ref(v_opts_2571_);
                if v___x_2573_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2564_);
                    v___x_2574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2574_, 0, v_msgData_2563_);
                    return v___x_2574_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2564_) == 0 {
                        v___x_2575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2575_, 0, v_msgData_2563_);
                        return v___x_2575_;
                    } else {
                        v_head_2576_ = crate::leanh::lean_ctor_get(v_macroStack_2564_, 0);
                        crate::leanh::lean_inc(v_head_2576_);
                        v_after_2577_ = crate::leanh::lean_ctor_get(v_head_2576_, 1);
                        v_isSharedCheck_2592_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2576_)) as u8;
                        if v_isSharedCheck_2592_ == 0 {
                            v_unused_2593_ = crate::leanh::lean_ctor_get(v_head_2576_, 0);
                            crate::leanh::lean_dec(v_unused_2593_);
                            v___x_2579_ = v_head_2576_;
                            v_isShared_2580_ = v_isSharedCheck_2592_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2577_);
                            crate::leanh::lean_dec(v_head_2576_);
                            v___x_2579_ = crate::leanh::lean_box(0);
                            v_isShared_2580_ = v_isSharedCheck_2592_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
                if v_isShared_2580_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2579_, 7);
                    crate::leanh::lean_ctor_set(v___x_2579_, 1, v___x_2581_);
                    crate::leanh::lean_ctor_set(v___x_2579_, 0, v_msgData_2563_);
                    v___x_2583_ = v___x_2579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_msgData_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2581_);
                    v___x_2583_ = v_reuseFailAlloc_2591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
                v___x_2585_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2585_, 0, v___x_2583_);
                crate::leanh::lean_ctor_set(v___x_2585_, 1, v___x_2584_);
                v___x_2586_ = l_Lean_MessageData_ofSyntax(v_after_2577_);
                v___x_2587_ = l_Lean_indentD(v___x_2586_);
                v_msgData_2588_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2588_, 0, v___x_2585_);
                crate::leanh::lean_ctor_set(v_msgData_2588_, 1, v___x_2587_);
                v___x_2589_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_2588_, v_macroStack_2564_);
                v___x_2590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2589_);
                return v___x_2590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(
    mut v_msgData_2594_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_2594_, v_macroStack_2595_, v___y_2596_);
    crate::leanh::lean_dec(v___y_2596_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(
    mut v_msg_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut v_a_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2603_ = l_Lean_Elab_Command_getRef___redArg(v___y_2600_);
                if crate::leanh::lean_obj_tag(v___x_2603_) == 0 {
                    v_a_2604_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                    crate::leanh::lean_inc(v_a_2604_);
                    crate::leanh::lean_dec_ref_known(v___x_2603_, 1);
                    v_macroStack_2605_ = crate::leanh::lean_ctor_get(v___y_2600_, 4);
                    v___x_2606_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_2599_, v___y_2601_);
                    v_a_2607_ = crate::leanh::lean_ctor_get(v___x_2606_, 0);
                    crate::leanh::lean_inc(v_a_2607_);
                    crate::leanh::lean_dec_ref(v___x_2606_);
                    v___x_2608_ = l_Lean_Elab_getBetterRef(v_a_2604_, v_macroStack_2605_);
                    crate::leanh::lean_dec(v_a_2604_);
                    crate::leanh::lean_inc(v_macroStack_2605_);
                    v___x_2609_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_2607_, v_macroStack_2605_, v___y_2601_);
                    v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2618_ = (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2618_ == 0 {
                        v___x_2612_ = v___x_2609_;
                        v_isShared_2613_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2610_);
                        crate::leanh::lean_dec(v___x_2609_);
                        v___x_2612_ = crate::leanh::lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2599_);
                    v_a_2619_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                    v_isSharedCheck_2626_ = (!crate::leanh::lean_is_exclusive(v___x_2603_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2621_ = v___x_2603_;
                        v_isShared_2622_ = v_isSharedCheck_2626_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2619_);
                        crate::leanh::lean_dec(v___x_2603_);
                        v___x_2621_ = crate::leanh::lean_box(0);
                        v_isShared_2622_ = v_isSharedCheck_2626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2608_);
                crate::leanh::lean_ctor_set(v___x_2614_, 1, v_a_2610_);
                if v_isShared_2613_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2612_, 1);
                    crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2614_);
                    v___x_2616_ = v___x_2612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
                    v___x_2616_ = v_reuseFailAlloc_2617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2616_;
            }
            3 => {
                if v_isShared_2622_ == 0 {
                    v___x_2624_ = v___x_2621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
                    v___x_2624_ = v_reuseFailAlloc_2625_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(
    mut v_msg_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_2627_, v___y_2628_, v___y_2629_);
    crate::leanh::lean_dec(v___y_2629_);
    crate::leanh::lean_dec_ref(v___y_2628_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
    mut v_ref_2632_: *mut crate::leanh::LeanObject,
    mut v_msg_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2648_: u8 = 0;
    let mut v_ref_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2637_ = l_Lean_Elab_Command_getRef___redArg(v___y_2634_);
                if crate::leanh::lean_obj_tag(v___x_2637_) == 0 {
                    v_a_2638_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                    crate::leanh::lean_inc(v_a_2638_);
                    crate::leanh::lean_dec_ref_known(v___x_2637_, 1);
                    v_fileName_2639_ = crate::leanh::lean_ctor_get(v___y_2634_, 0);
                    v_fileMap_2640_ = crate::leanh::lean_ctor_get(v___y_2634_, 1);
                    v_currRecDepth_2641_ = crate::leanh::lean_ctor_get(v___y_2634_, 2);
                    v_cmdPos_2642_ = crate::leanh::lean_ctor_get(v___y_2634_, 3);
                    v_macroStack_2643_ = crate::leanh::lean_ctor_get(v___y_2634_, 4);
                    v_quotContext_x3f_2644_ = crate::leanh::lean_ctor_get(v___y_2634_, 5);
                    v_currMacroScope_2645_ = crate::leanh::lean_ctor_get(v___y_2634_, 6);
                    v_snap_x3f_2646_ = crate::leanh::lean_ctor_get(v___y_2634_, 8);
                    v_cancelTk_x3f_2647_ = crate::leanh::lean_ctor_get(v___y_2634_, 9);
                    v_suppressElabErrors_2648_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2634_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_2649_ = l_Lean_replaceRef(v_ref_2632_, v_a_2638_);
                    crate::leanh::lean_dec(v_a_2638_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2647_);
                    crate::leanh::lean_inc(v_snap_x3f_2646_);
                    crate::leanh::lean_inc(v_currMacroScope_2645_);
                    crate::leanh::lean_inc(v_quotContext_x3f_2644_);
                    crate::leanh::lean_inc(v_macroStack_2643_);
                    crate::leanh::lean_inc(v_cmdPos_2642_);
                    crate::leanh::lean_inc(v_currRecDepth_2641_);
                    crate::leanh::lean_inc_ref(v_fileMap_2640_);
                    crate::leanh::lean_inc_ref(v_fileName_2639_);
                    v___x_2650_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2650_, 0, v_fileName_2639_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 1, v_fileMap_2640_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 2, v_currRecDepth_2641_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 3, v_cmdPos_2642_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 4, v_macroStack_2643_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 5, v_quotContext_x3f_2644_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 6, v_currMacroScope_2645_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 7, v_ref_2649_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 8, v_snap_x3f_2646_);
                    crate::leanh::lean_ctor_set(v___x_2650_, 9, v_cancelTk_x3f_2647_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2650_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2648_,
                    );
                    v___x_2651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_2633_, v___x_2650_, v___y_2635_);
                    crate::leanh::lean_dec_ref_known(v___x_2650_, 10);
                    return v___x_2651_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2633_);
                    v_a_2652_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                    v_isSharedCheck_2659_ = (!crate::leanh::lean_is_exclusive(v___x_2637_)) as u8;
                    if v_isSharedCheck_2659_ == 0 {
                        v___x_2654_ = v___x_2637_;
                        v_isShared_2655_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2652_);
                        crate::leanh::lean_dec(v___x_2637_);
                        v___x_2654_ = crate::leanh::lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2655_ == 0 {
                    v___x_2657_ = v___x_2654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
                    v___x_2657_ = v_reuseFailAlloc_2658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(
    mut v_ref_2660_: *mut crate::leanh::LeanObject,
    mut v_msg_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
        v_ref_2660_,
        v_msg_2661_,
        v___y_2662_,
        v___y_2663_,
    );
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec_ref(v___y_2662_);
    crate::leanh::lean_dec(v_ref_2660_);
    return v_res_2665_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(
    mut v_x_2666_: *mut crate::leanh::LeanObject,
    mut v_x_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: u64 = 0;
    let mut v___x_2676_: u64 = 0;
    let mut v___x_2677_: u64 = 0;
    let mut v_fold_2678_: u64 = 0;
    let mut v___x_2679_: u64 = 0;
    let mut v___x_2680_: u64 = 0;
    let mut v___x_2681_: u64 = 0;
    let mut v___x_2682_: usize = 0;
    let mut v___x_2683_: usize = 0;
    let mut v___x_2684_: usize = 0;
    let mut v___x_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2667_) == 0 {
                    return v_x_2666_;
                } else {
                    v_key_2668_ = crate::leanh::lean_ctor_get(v_x_2667_, 0);
                    v_value_2669_ = crate::leanh::lean_ctor_get(v_x_2667_, 1);
                    v_tail_2670_ = crate::leanh::lean_ctor_get(v_x_2667_, 2);
                    v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v_x_2667_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2672_ = v_x_2667_;
                        v_isShared_2673_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2670_);
                        crate::leanh::lean_inc(v_value_2669_);
                        crate::leanh::lean_inc(v_key_2668_);
                        crate::leanh::lean_dec(v_x_2667_);
                        v___x_2672_ = crate::leanh::lean_box(0);
                        v_isShared_2673_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2674_ = lean_array_get_size(v_x_2666_);
                v___x_2675_ = l_Lean_Syntax_instHashableRange_hash(v_key_2668_);
                v___x_2676_ = 32u64;
                v___x_2677_ = lean_uint64_shift_right(v___x_2675_, v___x_2676_);
                v_fold_2678_ = lean_uint64_xor(v___x_2675_, v___x_2677_);
                v___x_2679_ = 16u64;
                v___x_2680_ = lean_uint64_shift_right(v_fold_2678_, v___x_2679_);
                v___x_2681_ = lean_uint64_xor(v_fold_2678_, v___x_2680_);
                v___x_2682_ = lean_uint64_to_usize(v___x_2681_);
                v___x_2683_ = lean_usize_of_nat(v___x_2674_);
                v___x_2684_ = 1usize;
                v___x_2685_ = lean_usize_sub(v___x_2683_, v___x_2684_);
                v___x_2686_ = lean_usize_land(v___x_2682_, v___x_2685_);
                v___x_2687_ = lean_array_uget_borrowed(v_x_2666_, v___x_2686_);
                crate::leanh::lean_inc(v___x_2687_);
                if v_isShared_2673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2672_, 2, v___x_2687_);
                    v___x_2689_ = v___x_2672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_key_2668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_value_2669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2687_);
                    v___x_2689_ = v_reuseFailAlloc_2692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2690_ = lean_array_uset(v_x_2666_, v___x_2686_, v___x_2689_);
                v_x_2666_ = v___x_2690_;
                v_x_2667_ = v_tail_2670_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(
    mut v_i_2694_: *mut crate::leanh::LeanObject,
    mut v_source_2695_: *mut crate::leanh::LeanObject,
    mut v_target_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v_es_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2697_ = lean_array_get_size(v_source_2695_);
                v___x_2698_ = lean_nat_dec_lt(v_i_2694_, v___x_2697_);
                if v___x_2698_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2695_);
                    crate::leanh::lean_dec(v_i_2694_);
                    return v_target_2696_;
                } else {
                    v_es_2699_ = lean_array_fget(v_source_2695_, v_i_2694_);
                    v___x_2700_ = crate::leanh::lean_box(0);
                    v_source_2701_ = lean_array_fset(v_source_2695_, v_i_2694_, v___x_2700_);
                    v_target_2702_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_2696_, v_es_2699_);
                    v___x_2703_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2704_ = lean_nat_add(v_i_2694_, v___x_2703_);
                    crate::leanh::lean_dec(v_i_2694_);
                    v_i_2694_ = v___x_2704_;
                    v_source_2695_ = v_source_2701_;
                    v_target_2696_ = v_target_2702_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(
    mut v_data_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = lean_array_get_size(v_data_2706_);
    v___x_2708_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2709_ = lean_nat_mul(v___x_2707_, v___x_2708_);
    v___x_2710_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2711_ = crate::leanh::lean_box(0);
    v___x_2712_ = lean_mk_array(v_nbuckets_2709_, v___x_2711_);
    v___x_2713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_2710_, v_data_2706_, v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_x_2715_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2716_: u8 = 0;
    let mut v_key_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2715_) == 0 {
                    v___x_2716_ = 0;
                    return v___x_2716_;
                } else {
                    v_key_2717_ = crate::leanh::lean_ctor_get(v_x_2715_, 0);
                    v_tail_2718_ = crate::leanh::lean_ctor_get(v_x_2715_, 2);
                    v___x_2719_ = l_Lean_Syntax_instBEqRange_beq(v_key_2717_, v_a_2714_);
                    if v___x_2719_ == 0 {
                        v_x_2715_ = v_tail_2718_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2719_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_x_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2723_: u8 = 0;
    let mut v_r_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_2721_, v_x_2722_);
    crate::leanh::lean_dec(v_x_2722_);
    crate::leanh::lean_dec_ref(v_a_2721_);
    v_r_2724_ = crate::leanh::lean_box((v_res_2723_) as usize);
    return v_r_2724_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_b_2726_: *mut crate::leanh::LeanObject,
    mut v_x_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2727_) == 0 {
                    crate::leanh::lean_dec(v_b_2726_);
                    crate::leanh::lean_dec_ref(v_a_2725_);
                    return v_x_2727_;
                } else {
                    v_key_2728_ = crate::leanh::lean_ctor_get(v_x_2727_, 0);
                    v_value_2729_ = crate::leanh::lean_ctor_get(v_x_2727_, 1);
                    v_tail_2730_ = crate::leanh::lean_ctor_get(v_x_2727_, 2);
                    v_isSharedCheck_2742_ = (!crate::leanh::lean_is_exclusive(v_x_2727_)) as u8;
                    if v_isSharedCheck_2742_ == 0 {
                        v___x_2732_ = v_x_2727_;
                        v_isShared_2733_ = v_isSharedCheck_2742_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2730_);
                        crate::leanh::lean_inc(v_value_2729_);
                        crate::leanh::lean_inc(v_key_2728_);
                        crate::leanh::lean_dec(v_x_2727_);
                        v___x_2732_ = crate::leanh::lean_box(0);
                        v_isShared_2733_ = v_isSharedCheck_2742_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2734_ = l_Lean_Syntax_instBEqRange_beq(v_key_2728_, v_a_2725_);
                if v___x_2734_ == 0 {
                    v___x_2735_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_2725_, v_b_2726_, v_tail_2730_);
                    if v_isShared_2733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2732_, 2, v___x_2735_);
                        v___x_2737_ = v___x_2732_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_key_2728_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_value_2729_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 2, v___x_2735_);
                        v___x_2737_ = v_reuseFailAlloc_2738_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2729_);
                    crate::leanh::lean_dec(v_key_2728_);
                    if v_isShared_2733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2732_, 1, v_b_2726_);
                        crate::leanh::lean_ctor_set(v___x_2732_, 0, v_a_2725_);
                        v___x_2740_ = v___x_2732_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2741_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2725_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_b_2726_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_tail_2730_);
                        v___x_2740_ = v_reuseFailAlloc_2741_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2737_;
            }
            3 => {
                return v___x_2740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(
    mut v_m_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_b_2745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u64 = 0;
    let mut v___x_2753_: u64 = 0;
    let mut v___x_2754_: u64 = 0;
    let mut v_fold_2755_: u64 = 0;
    let mut v___x_2756_: u64 = 0;
    let mut v___x_2757_: u64 = 0;
    let mut v___x_2758_: u64 = 0;
    let mut v___x_2759_: usize = 0;
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v_bkt_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v_val_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2746_ = crate::leanh::lean_ctor_get(v_m_2743_, 0);
                v_buckets_2747_ = crate::leanh::lean_ctor_get(v_m_2743_, 1);
                v_isSharedCheck_2790_ = (!crate::leanh::lean_is_exclusive(v_m_2743_)) as u8;
                if v_isSharedCheck_2790_ == 0 {
                    v___x_2749_ = v_m_2743_;
                    v_isShared_2750_ = v_isSharedCheck_2790_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2747_);
                    crate::leanh::lean_inc(v_size_2746_);
                    crate::leanh::lean_dec(v_m_2743_);
                    v___x_2749_ = crate::leanh::lean_box(0);
                    v_isShared_2750_ = v_isSharedCheck_2790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2751_ = lean_array_get_size(v_buckets_2747_);
                v___x_2752_ = l_Lean_Syntax_instHashableRange_hash(v_a_2744_);
                v___x_2753_ = 32u64;
                v___x_2754_ = lean_uint64_shift_right(v___x_2752_, v___x_2753_);
                v_fold_2755_ = lean_uint64_xor(v___x_2752_, v___x_2754_);
                v___x_2756_ = 16u64;
                v___x_2757_ = lean_uint64_shift_right(v_fold_2755_, v___x_2756_);
                v___x_2758_ = lean_uint64_xor(v_fold_2755_, v___x_2757_);
                v___x_2759_ = lean_uint64_to_usize(v___x_2758_);
                v___x_2760_ = lean_usize_of_nat(v___x_2751_);
                v___x_2761_ = 1usize;
                v___x_2762_ = lean_usize_sub(v___x_2760_, v___x_2761_);
                v___x_2763_ = lean_usize_land(v___x_2759_, v___x_2762_);
                v_bkt_2764_ = lean_array_uget_borrowed(v_buckets_2747_, v___x_2763_);
                v___x_2765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_2744_, v_bkt_2764_);
                if v___x_2765_ == 0 {
                    v___x_2766_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2767_ = lean_nat_add(v_size_2746_, v___x_2766_);
                    crate::leanh::lean_dec(v_size_2746_);
                    crate::leanh::lean_inc(v_bkt_2764_);
                    v___x_2768_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2768_, 0, v_a_2744_);
                    crate::leanh::lean_ctor_set(v___x_2768_, 1, v_b_2745_);
                    crate::leanh::lean_ctor_set(v___x_2768_, 2, v_bkt_2764_);
                    v_buckets_x27_2769_ =
                        lean_array_uset(v_buckets_2747_, v___x_2763_, v___x_2768_);
                    v___x_2770_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2771_ = lean_nat_mul(v_size_x27_2767_, v___x_2770_);
                    v___x_2772_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2773_ = lean_nat_div(v___x_2771_, v___x_2772_);
                    crate::leanh::lean_dec(v___x_2771_);
                    v___x_2774_ = lean_array_get_size(v_buckets_x27_2769_);
                    v___x_2775_ = lean_nat_dec_le(v___x_2773_, v___x_2774_);
                    crate::leanh::lean_dec(v___x_2773_);
                    if v___x_2775_ == 0 {
                        v_val_2776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_2769_);
                        if v_isShared_2750_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2749_, 1, v_val_2776_);
                            crate::leanh::lean_ctor_set(v___x_2749_, 0, v_size_x27_2767_);
                            v___x_2778_ = v___x_2749_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2779_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2779_,
                                0,
                                v_size_x27_2767_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_val_2776_);
                            v___x_2778_ = v_reuseFailAlloc_2779_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2750_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2749_, 1, v_buckets_x27_2769_);
                            crate::leanh::lean_ctor_set(v___x_2749_, 0, v_size_x27_2767_);
                            v___x_2781_ = v___x_2749_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2782_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2782_,
                                0,
                                v_size_x27_2767_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2782_,
                                1,
                                v_buckets_x27_2769_,
                            );
                            v___x_2781_ = v_reuseFailAlloc_2782_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2764_);
                    v___x_2783_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2784_ =
                        lean_array_uset(v_buckets_2747_, v___x_2763_, v___x_2783_);
                    v___x_2785_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_2744_, v_b_2745_, v_bkt_2764_);
                    v___x_2786_ = lean_array_uset(v_buckets_x27_2784_, v___x_2763_, v___x_2785_);
                    if v_isShared_2750_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2749_, 1, v___x_2786_);
                        v___x_2788_ = v___x_2749_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_size_2746_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
                        v___x_2788_ = v_reuseFailAlloc_2789_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2778_;
            }
            3 => {
                return v___x_2781_;
            }
            4 => {
                return v___x_2788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1;
    v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
    return v___x_2795_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3;
    v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
    return v___x_2798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(
    mut v_val_2811_: *mut crate::leanh::LeanObject,
    mut v___x_2812_: u8,
    mut v_ci_2813_: *mut crate::leanh::LeanObject,
    mut v_info_2814_: *mut crate::leanh::LeanObject,
    mut v_x_2815_: *mut crate::leanh::LeanObject,
    mut v___y_2816_: *mut crate::leanh::LeanObject,
    mut v___y_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v_maskAcc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v_snd_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_unused_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_unused_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_2814_) == 10 {
                    v_i_2819_ = crate::leanh::lean_ctor_get(v_info_2814_, 0);
                    crate::leanh::lean_inc_ref(v_i_2819_);
                    v_stx_2820_ = crate::leanh::lean_ctor_get(v_i_2819_, 0);
                    v_value_2821_ = crate::leanh::lean_ctor_get(v_i_2819_, 1);
                    v_isSharedCheck_2916_ = (!crate::leanh::lean_is_exclusive(v_i_2819_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2823_ = v_i_2819_;
                        v_isShared_2824_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2821_);
                        crate::leanh::lean_inc(v_stx_2820_);
                        crate::leanh::lean_dec(v_i_2819_);
                        v___x_2823_ = crate::leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_2814_);
                    v___x_2917_ = crate::leanh::lean_box(0);
                    v___x_2918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2918_, 0, v___x_2917_);
                    return v___x_2918_;
                }
            }
            1 => {
                v___x_2825_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
                v___x_2826_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_value_2821_,
                    v___x_2825_,
                );
                crate::leanh::lean_dec(v_value_2821_);
                if crate::leanh::lean_obj_tag(v___x_2826_) == 1 {
                    v_val_2827_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                    v_isSharedCheck_2906_ = (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2829_ = v___x_2826_;
                        v_isShared_2830_ = v_isSharedCheck_2906_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2827_);
                        crate::leanh::lean_dec(v___x_2826_);
                        v___x_2829_ = crate::leanh::lean_box(0);
                        v_isShared_2830_ = v_isSharedCheck_2906_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2826_);
                    crate::leanh::lean_del_object(v___x_2823_);
                    crate::leanh::lean_dec(v_stx_2820_);
                    v_isSharedCheck_2914_ = (!crate::leanh::lean_is_exclusive(v_info_2814_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v_unused_2915_ = crate::leanh::lean_ctor_get(v_info_2814_, 0);
                        crate::leanh::lean_dec(v_unused_2915_);
                        v___x_2908_ = v_info_2814_;
                        v_isShared_2909_ = v_isSharedCheck_2914_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_info_2814_);
                        v___x_2908_ = crate::leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2914_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2831_ = l_Lean_Elab_Info_range_x3f(v_info_2814_);
                if crate::leanh::lean_obj_tag(v___x_2831_) == 1 {
                    v_val_2832_ = crate::leanh::lean_ctor_get(v___x_2831_, 0);
                    v_isSharedCheck_2901_ = (!crate::leanh::lean_is_exclusive(v___x_2831_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2834_ = v___x_2831_;
                        v_isShared_2835_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2832_);
                        crate::leanh::lean_dec(v___x_2831_);
                        v___x_2834_ = crate::leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2831_);
                    crate::leanh::lean_dec(v_val_2827_);
                    crate::leanh::lean_del_object(v___x_2823_);
                    crate::leanh::lean_dec(v_stx_2820_);
                    crate::leanh::lean_dec_ref_known(v_info_2814_, 1);
                    v___x_2902_ = crate::leanh::lean_box(0);
                    if v_isShared_2830_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2829_, 0);
                        crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2902_);
                        v___x_2904_ = v___x_2829_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
                        v___x_2904_ = v_reuseFailAlloc_2905_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6;
                crate::leanh::lean_inc(v_stx_2820_);
                v___x_2889_ = l_Lean_Syntax_isOfKind(v_stx_2820_, v___x_2888_);
                if v___x_2889_ == 0 {
                    v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8;
                    crate::leanh::lean_inc(v_stx_2820_);
                    v___x_2891_ = l_Lean_Syntax_isOfKind(v_stx_2820_, v___x_2890_);
                    if v___x_2891_ == 0 {
                        crate::leanh::lean_del_object(v___x_2834_);
                        crate::leanh::lean_dec(v_val_2832_);
                        crate::leanh::lean_del_object(v___x_2829_);
                        crate::leanh::lean_dec(v_val_2827_);
                        crate::leanh::lean_del_object(v___x_2823_);
                        crate::leanh::lean_dec(v_stx_2820_);
                        v_isSharedCheck_2899_ =
                            (!crate::leanh::lean_is_exclusive(v_info_2814_)) as u8;
                        if v_isSharedCheck_2899_ == 0 {
                            v_unused_2900_ = crate::leanh::lean_ctor_get(v_info_2814_, 0);
                            crate::leanh::lean_dec(v_unused_2900_);
                            v___x_2893_ = v_info_2814_;
                            v_isShared_2894_ = v_isSharedCheck_2899_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_info_2814_);
                            v___x_2893_ = crate::leanh::lean_box(0);
                            v_isShared_2894_ = v_isSharedCheck_2899_;
                            state = 14;
                            continue;
                        }
                    } else {
                        state = 8;
                        continue;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            4 => {
                v___x_2838_ = lean_st_ref_take(v_val_2811_);
                if v_isShared_2824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2823_, 1, v_maskAcc_2837_);
                    v___x_2840_ = v___x_2823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_stx_2820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_maskAcc_2837_);
                    v___x_2840_ = v_reuseFailAlloc_2846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_2838_, v_val_2832_, v___x_2840_);
                v___x_2842_ = lean_st_ref_set(v_val_2811_, v___x_2841_);
                if v_isShared_2835_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2834_, 0);
                    crate::leanh::lean_ctor_set(v___x_2834_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2844_;
            }
            7 => {
                v___x_2849_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0;
                v___x_2851_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
                    v___x_2812_,
                    v_val_2827_,
                    v___y_2848_,
                    v___x_2849_,
                    v___x_2850_,
                );
                crate::leanh::lean_dec_ref(v___y_2848_);
                crate::leanh::lean_dec(v_val_2827_);
                v_maskAcc_2837_ = v___x_2851_;
                state = 4;
                continue;
            }
            8 => {
                v___x_2853_ = lean_st_ref_get(v_val_2811_);
                v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_2853_, v_val_2832_);
                crate::leanh::lean_dec(v___x_2853_);
                if crate::leanh::lean_obj_tag(v___x_2854_) == 1 {
                    v_val_2855_ = crate::leanh::lean_ctor_get(v___x_2854_, 0);
                    v_isSharedCheck_2887_ = (!crate::leanh::lean_is_exclusive(v___x_2854_)) as u8;
                    if v_isSharedCheck_2887_ == 0 {
                        v___x_2857_ = v___x_2854_;
                        v_isShared_2858_ = v_isSharedCheck_2887_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2855_);
                        crate::leanh::lean_dec(v___x_2854_);
                        v___x_2857_ = crate::leanh::lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2887_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2854_);
                    crate::leanh::lean_del_object(v___x_2829_);
                    crate::leanh::lean_dec_ref_known(v_info_2814_, 1);
                    v_maskAcc_2837_ = v_val_2827_;
                    state = 4;
                    continue;
                }
            }
            9 => {
                v_snd_2859_ = crate::leanh::lean_ctor_get(v_val_2855_, 1);
                v_isSharedCheck_2885_ = (!crate::leanh::lean_is_exclusive(v_val_2855_)) as u8;
                if v_isSharedCheck_2885_ == 0 {
                    v_unused_2886_ = crate::leanh::lean_ctor_get(v_val_2855_, 0);
                    crate::leanh::lean_dec(v_unused_2886_);
                    v___x_2861_ = v_val_2855_;
                    v_isShared_2862_ = v_isSharedCheck_2885_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2859_);
                    crate::leanh::lean_dec(v_val_2855_);
                    v___x_2861_ = crate::leanh::lean_box(0);
                    v_isShared_2862_ = v_isSharedCheck_2885_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2863_ = lean_array_get_size(v_val_2827_);
                v___x_2864_ = lean_array_get_size(v_snd_2859_);
                v___x_2865_ = lean_nat_dec_eq(v___x_2863_, v___x_2864_);
                if v___x_2865_ == 0 {
                    v___x_2866_ = l_Lean_Elab_Info_stx(v_info_2814_);
                    crate::leanh::lean_dec_ref_known(v_info_2814_, 1);
                    v___x_2867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
                    v___x_2868_ = l_Nat_reprFast(v___x_2864_);
                    if v_isShared_2858_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2857_, 3);
                        crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2868_);
                        v___x_2870_ = v___x_2857_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2884_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2868_);
                        v___x_2870_ = v_reuseFailAlloc_2884_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2861_);
                    crate::leanh::lean_del_object(v___x_2857_);
                    crate::leanh::lean_del_object(v___x_2829_);
                    crate::leanh::lean_dec_ref_known(v_info_2814_, 1);
                    v___y_2848_ = v_snd_2859_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                v___x_2871_ = l_Lean_MessageData_ofFormat(v___x_2870_);
                if v_isShared_2862_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2861_, 7);
                    crate::leanh::lean_ctor_set(v___x_2861_, 1, v___x_2871_);
                    crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2867_);
                    v___x_2873_ = v___x_2861_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2871_);
                    v___x_2873_ = v_reuseFailAlloc_2883_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
                v___x_2875_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2875_, 0, v___x_2873_);
                crate::leanh::lean_ctor_set(v___x_2875_, 1, v___x_2874_);
                v___x_2876_ = l_Nat_reprFast(v___x_2863_);
                if v_isShared_2830_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2829_, 3);
                    crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2876_);
                    v___x_2878_ = v___x_2829_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2882_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
                    v___x_2878_ = v_reuseFailAlloc_2882_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2879_ = l_Lean_MessageData_ofFormat(v___x_2878_);
                v___x_2880_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2880_, 0, v___x_2875_);
                crate::leanh::lean_ctor_set(v___x_2880_, 1, v___x_2879_);
                v___x_2881_ =
                    l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
                        v___x_2866_,
                        v___x_2880_,
                        v___y_2816_,
                        v___y_2817_,
                    );
                crate::leanh::lean_dec(v___x_2866_);
                if crate::leanh::lean_obj_tag(v___x_2881_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2881_, 1);
                    v___y_2848_ = v_snd_2859_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2859_);
                    crate::leanh::lean_del_object(v___x_2834_);
                    crate::leanh::lean_dec(v_val_2832_);
                    crate::leanh::lean_dec(v_val_2827_);
                    crate::leanh::lean_del_object(v___x_2823_);
                    crate::leanh::lean_dec(v_stx_2820_);
                    return v___x_2881_;
                }
            }
            14 => {
                v___x_2895_ = crate::leanh::lean_box(0);
                if v_isShared_2894_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2893_, 0);
                    crate::leanh::lean_ctor_set(v___x_2893_, 0, v___x_2895_);
                    v___x_2897_ = v___x_2893_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
                    v___x_2897_ = v_reuseFailAlloc_2898_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2897_;
            }
            16 => {
                return v___x_2904_;
            }
            17 => {
                v___x_2910_ = crate::leanh::lean_box(0);
                if v_isShared_2909_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2908_, 0);
                    crate::leanh::lean_ctor_set(v___x_2908_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2908_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(
    mut v_val_2919_: *mut crate::leanh::LeanObject,
    mut v___x_2920_: *mut crate::leanh::LeanObject,
    mut v_ci_2921_: *mut crate::leanh::LeanObject,
    mut v_info_2922_: *mut crate::leanh::LeanObject,
    mut v_x_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14717__boxed_2927_: u8 = 0;
    let mut v_res_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14717__boxed_2927_ = (crate::leanh::lean_unbox(v___x_2920_) as u8);
    v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v_val_2919_, v___x_14717__boxed_2927_, v_ci_2921_, v_info_2922_, v_x_2923_, v___y_2924_, v___y_2925_);
    crate::leanh::lean_dec(v___y_2925_);
    crate::leanh::lean_dec_ref(v___y_2924_);
    crate::leanh::lean_dec_ref(v_x_2923_);
    crate::leanh::lean_dec_ref(v_ci_2921_);
    crate::leanh::lean_dec(v_val_2919_);
    return v_res_2928_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(
    mut v_postNode_2929_: *mut crate::leanh::LeanObject,
    mut v_ci_2930_: *mut crate::leanh::LeanObject,
    mut v_i_2931_: *mut crate::leanh::LeanObject,
    mut v_cs_2932_: *mut crate::leanh::LeanObject,
    mut v_x_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2935_);
    crate::leanh::lean_inc_ref(v___y_2934_);
    v___x_2937_ = crate::leanh::lean_apply_6(
        v_postNode_2929_,
        v_ci_2930_,
        v_i_2931_,
        v_cs_2932_,
        v___y_2934_,
        v___y_2935_,
        crate::leanh::lean_box(0),
    );
    return v___x_2937_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(
    mut v_postNode_2938_: *mut crate::leanh::LeanObject,
    mut v_ci_2939_: *mut crate::leanh::LeanObject,
    mut v_i_2940_: *mut crate::leanh::LeanObject,
    mut v_cs_2941_: *mut crate::leanh::LeanObject,
    mut v_x_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2946_ =
        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(
            v_postNode_2938_,
            v_ci_2939_,
            v_i_2940_,
            v_cs_2941_,
            v_x_2942_,
            v___y_2943_,
            v___y_2944_,
        );
    crate::leanh::lean_dec(v___y_2944_);
    crate::leanh::lean_dec_ref(v___y_2943_);
    crate::leanh::lean_dec(v_x_2942_);
    return v_res_2946_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2947_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(
    mut v_msg_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v_toFunctor_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___f_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_13235__overap_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
                v___x_2955_ = l_StateRefT_x27_instMonad___redArg(v___x_2954_);
                v_toApplicative_2956_ = crate::leanh::lean_ctor_get(v___x_2955_, 0);
                v_isSharedCheck_2987_ = (!crate::leanh::lean_is_exclusive(v___x_2955_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v_unused_2988_ = crate::leanh::lean_ctor_get(v___x_2955_, 1);
                    crate::leanh::lean_dec(v_unused_2988_);
                    v___x_2958_ = v___x_2955_;
                    v_isShared_2959_ = v_isSharedCheck_2987_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2956_);
                    crate::leanh::lean_dec(v___x_2955_);
                    v___x_2958_ = crate::leanh::lean_box(0);
                    v_isShared_2959_ = v_isSharedCheck_2987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2960_ = crate::leanh::lean_ctor_get(v_toApplicative_2956_, 0);
                v_toSeq_2961_ = crate::leanh::lean_ctor_get(v_toApplicative_2956_, 2);
                v_toSeqLeft_2962_ = crate::leanh::lean_ctor_get(v_toApplicative_2956_, 3);
                v_toSeqRight_2963_ = crate::leanh::lean_ctor_get(v_toApplicative_2956_, 4);
                v_isSharedCheck_2985_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2956_)) as u8;
                if v_isSharedCheck_2985_ == 0 {
                    v_unused_2986_ = crate::leanh::lean_ctor_get(v_toApplicative_2956_, 1);
                    crate::leanh::lean_dec(v_unused_2986_);
                    v___x_2965_ = v_toApplicative_2956_;
                    v_isShared_2966_ = v_isSharedCheck_2985_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2963_);
                    crate::leanh::lean_inc(v_toSeqLeft_2962_);
                    crate::leanh::lean_inc(v_toSeq_2961_);
                    crate::leanh::lean_inc(v_toFunctor_2960_);
                    crate::leanh::lean_dec(v_toApplicative_2956_);
                    v___x_2965_ = crate::leanh::lean_box(0);
                    v_isShared_2966_ = v_isSharedCheck_2985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2967_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1;
                v___f_2968_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2960_);
                v___f_2969_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2969_, 0, v_toFunctor_2960_);
                v___f_2970_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2970_, 0, v_toFunctor_2960_);
                v___x_2971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2971_, 0, v___f_2969_);
                crate::leanh::lean_ctor_set(v___x_2971_, 1, v___f_2970_);
                v___f_2972_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2972_, 0, v_toSeqRight_2963_);
                v___f_2973_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2973_, 0, v_toSeqLeft_2962_);
                v___f_2974_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2974_, 0, v_toSeq_2961_);
                if v_isShared_2966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2965_, 4, v___f_2972_);
                    crate::leanh::lean_ctor_set(v___x_2965_, 3, v___f_2973_);
                    crate::leanh::lean_ctor_set(v___x_2965_, 2, v___f_2974_);
                    crate::leanh::lean_ctor_set(v___x_2965_, 1, v___f_2967_);
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2971_);
                    v___x_2976_ = v___x_2965_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___f_2967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 2, v___f_2974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 3, v___f_2973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 4, v___f_2972_);
                    v___x_2976_ = v_reuseFailAlloc_2984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2958_, 1, v___f_2968_);
                    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___x_2976_);
                    v___x_2978_ = v___x_2958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___f_2968_);
                    v___x_2978_ = v_reuseFailAlloc_2983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2979_ = crate::leanh::lean_box(0);
                v___x_2980_ = l_instInhabitedOfMonad___redArg(v___x_2978_, v___x_2979_);
                v___x_13235__overap_2981_ = lean_panic_fn_borrowed(v___x_2980_, v_msg_2950_);
                crate::leanh::lean_dec(v___x_2980_);
                crate::leanh::lean_inc(v___y_2952_);
                crate::leanh::lean_inc_ref(v___y_2951_);
                v___x_2982_ = crate::leanh::lean_apply_3(
                    v___x_13235__overap_2981_,
                    v___y_2951_,
                    v___y_2952_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(
    mut v_msg_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_2989_, v___y_2990_, v___y_2991_);
    crate::leanh::lean_dec(v___y_2991_);
    crate::leanh::lean_dec_ref(v___y_2990_);
    return v_res_2993_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2997_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2;
    v___x_2998_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2999_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_3000_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1;
    v___x_3001_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0;
    v___x_3002_ = l_mkPanicMessageWithDecl(
        v___x_3001_,
        v___x_3000_,
        v___x_2999_,
        v___x_2998_,
        v___x_2997_,
    );
    return v___x_3002_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(
    mut v_preNode_3003_: *mut crate::leanh::LeanObject,
    mut v_postNode_3004_: *mut crate::leanh::LeanObject,
    mut v_x_3005_: *mut crate::leanh::LeanObject,
    mut v_x_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_unused_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_a_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_a_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut v_unused_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3006_) {
                0 => {
                    v_i_3010_ = crate::leanh::lean_ctor_get(v_x_3006_, 0);
                    crate::leanh::lean_inc_ref(v_i_3010_);
                    v_t_3011_ = crate::leanh::lean_ctor_get(v_x_3006_, 1);
                    crate::leanh::lean_inc_ref(v_t_3011_);
                    crate::leanh::lean_dec_ref_known(v_x_3006_, 2);
                    v___x_3012_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3010_, v_x_3005_);
                    v_x_3005_ = v___x_3012_;
                    v_x_3006_ = v_t_3011_;
                    state = 0;
                    continue;
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_3005_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_3006_, 2);
                        crate::leanh::lean_dec_ref(v_postNode_3004_);
                        crate::leanh::lean_dec_ref(v_preNode_3003_);
                        v___x_3014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
                        v___x_3015_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_3014_, v___y_3007_, v___y_3008_);
                        return v___x_3015_;
                    } else {
                        v_i_3016_ = crate::leanh::lean_ctor_get(v_x_3006_, 0);
                        crate::leanh::lean_inc_ref_n(v_i_3016_, 2);
                        v_children_3017_ = crate::leanh::lean_ctor_get(v_x_3006_, 1);
                        crate::leanh::lean_inc_ref_n(v_children_3017_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_3006_, 2);
                        v_val_3018_ = crate::leanh::lean_ctor_get(v_x_3005_, 0);
                        crate::leanh::lean_inc_n(v_val_3018_, 2);
                        crate::leanh::lean_inc_ref(v_preNode_3003_);
                        crate::leanh::lean_inc(v___y_3008_);
                        crate::leanh::lean_inc_ref(v___y_3007_);
                        v___x_3019_ = crate::leanh::lean_apply_6(
                            v_preNode_3003_,
                            v_val_3018_,
                            v_i_3016_,
                            v_children_3017_,
                            v___y_3007_,
                            v___y_3008_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                            v_a_3020_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                            crate::leanh::lean_inc(v_a_3020_);
                            crate::leanh::lean_dec_ref_known(v___x_3019_, 1);
                            v___x_3021_ = (crate::leanh::lean_unbox(v_a_3020_) as u8);
                            crate::leanh::lean_dec(v_a_3020_);
                            if v___x_3021_ == 0 {
                                crate::leanh::lean_dec_ref(v_preNode_3003_);
                                v_isSharedCheck_3046_ =
                                    (!crate::leanh::lean_is_exclusive(v_x_3005_)) as u8;
                                if v_isSharedCheck_3046_ == 0 {
                                    v_unused_3047_ = crate::leanh::lean_ctor_get(v_x_3005_, 0);
                                    crate::leanh::lean_dec(v_unused_3047_);
                                    v___x_3023_ = v_x_3005_;
                                    v_isShared_3024_ = v_isSharedCheck_3046_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_x_3005_);
                                    v___x_3023_ = crate::leanh::lean_box(0);
                                    v_isShared_3024_ = v_isSharedCheck_3046_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_3048_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_3005_, v_i_3016_);
                                v___x_3049_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_3017_);
                                v___x_3050_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_ref(v_postNode_3004_);
                                v___x_3051_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3003_, v_postNode_3004_, v___x_3048_, v___x_3049_, v___x_3050_, v___y_3007_, v___y_3008_);
                                if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                                    v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                                    crate::leanh::lean_inc(v_a_3052_);
                                    crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                                    crate::leanh::lean_inc(v___y_3008_);
                                    crate::leanh::lean_inc_ref(v___y_3007_);
                                    v___x_3053_ = crate::leanh::lean_apply_7(
                                        v_postNode_3004_,
                                        v_val_3018_,
                                        v_i_3016_,
                                        v_children_3017_,
                                        v_a_3052_,
                                        v___y_3007_,
                                        v___y_3008_,
                                        crate::leanh::lean_box(0),
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3053_) == 0 {
                                        v_a_3054_ = crate::leanh::lean_ctor_get(v___x_3053_, 0);
                                        v_isSharedCheck_3062_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3053_)) as u8;
                                        if v_isSharedCheck_3062_ == 0 {
                                            v___x_3056_ = v___x_3053_;
                                            v_isShared_3057_ = v_isSharedCheck_3062_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3054_);
                                            crate::leanh::lean_dec(v___x_3053_);
                                            v___x_3056_ = crate::leanh::lean_box(0);
                                            v_isShared_3057_ = v_isSharedCheck_3062_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3053_, 0);
                                        v_isSharedCheck_3070_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3053_)) as u8;
                                        if v_isSharedCheck_3070_ == 0 {
                                            v___x_3065_ = v___x_3053_;
                                            v_isShared_3066_ = v_isSharedCheck_3070_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3063_);
                                            crate::leanh::lean_dec(v___x_3053_);
                                            v___x_3065_ = crate::leanh::lean_box(0);
                                            v_isShared_3066_ = v_isSharedCheck_3070_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_3018_);
                                    crate::leanh::lean_dec_ref(v_children_3017_);
                                    crate::leanh::lean_dec_ref(v_i_3016_);
                                    crate::leanh::lean_dec_ref(v_postNode_3004_);
                                    v_a_3071_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                                    v_isSharedCheck_3078_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3051_)) as u8;
                                    if v_isSharedCheck_3078_ == 0 {
                                        v___x_3073_ = v___x_3051_;
                                        v_isShared_3074_ = v_isSharedCheck_3078_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3071_);
                                        crate::leanh::lean_dec(v___x_3051_);
                                        v___x_3073_ = crate::leanh::lean_box(0);
                                        v_isShared_3074_ = v_isSharedCheck_3078_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3018_);
                            crate::leanh::lean_dec_ref(v_children_3017_);
                            crate::leanh::lean_dec_ref_known(v_x_3005_, 1);
                            crate::leanh::lean_dec_ref(v_i_3016_);
                            crate::leanh::lean_dec_ref(v_postNode_3004_);
                            crate::leanh::lean_dec_ref(v_preNode_3003_);
                            v_a_3079_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                            v_isSharedCheck_3086_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                            if v_isSharedCheck_3086_ == 0 {
                                v___x_3081_ = v___x_3019_;
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3079_);
                                crate::leanh::lean_dec(v___x_3019_);
                                v___x_3081_ = crate::leanh::lean_box(0);
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_3005_);
                    crate::leanh::lean_dec_ref(v_postNode_3004_);
                    crate::leanh::lean_dec_ref(v_preNode_3003_);
                    v_isSharedCheck_3094_ = (!crate::leanh::lean_is_exclusive(v_x_3006_)) as u8;
                    if v_isSharedCheck_3094_ == 0 {
                        v_unused_3095_ = crate::leanh::lean_ctor_get(v_x_3006_, 0);
                        crate::leanh::lean_dec(v_unused_3095_);
                        v___x_3088_ = v_x_3006_;
                        v_isShared_3089_ = v_isSharedCheck_3094_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3006_);
                        v___x_3088_ = crate::leanh::lean_box(0);
                        v_isShared_3089_ = v_isSharedCheck_3094_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3025_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_3008_);
                crate::leanh::lean_inc_ref(v___y_3007_);
                v___x_3026_ = crate::leanh::lean_apply_7(
                    v_postNode_3004_,
                    v_val_3018_,
                    v_i_3016_,
                    v_children_3017_,
                    v___x_3025_,
                    v___y_3007_,
                    v___y_3008_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3026_) == 0 {
                    v_a_3027_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
                    v_isSharedCheck_3037_ = (!crate::leanh::lean_is_exclusive(v___x_3026_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3029_ = v___x_3026_;
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3027_);
                        crate::leanh::lean_dec(v___x_3026_);
                        v___x_3029_ = crate::leanh::lean_box(0);
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3023_);
                    v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
                    v_isSharedCheck_3045_ = (!crate::leanh::lean_is_exclusive(v___x_3026_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_3040_ = v___x_3026_;
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3038_);
                        crate::leanh::lean_dec(v___x_3026_);
                        v___x_3040_ = crate::leanh::lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3023_, 0, v_a_3027_);
                    v___x_3032_ = v___x_3023_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3032_);
                    v___x_3034_ = v___x_3029_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3034_;
            }
            5 => {
                if v_isShared_3041_ == 0 {
                    v___x_3043_ = v___x_3040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
                    v___x_3043_ = v_reuseFailAlloc_3044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3043_;
            }
            7 => {
                v___x_3058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v_a_3054_);
                if v_isShared_3057_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3056_, 0, v___x_3058_);
                    v___x_3060_ = v___x_3056_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3060_;
            }
            9 => {
                if v_isShared_3066_ == 0 {
                    v___x_3068_ = v___x_3065_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
                    v___x_3068_ = v_reuseFailAlloc_3069_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3068_;
            }
            11 => {
                if v_isShared_3074_ == 0 {
                    v___x_3076_ = v___x_3073_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
                    v___x_3076_ = v_reuseFailAlloc_3077_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3076_;
            }
            13 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3084_;
            }
            15 => {
                v___x_3090_ = crate::leanh::lean_box(0);
                if v_isShared_3089_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3088_, 0);
                    crate::leanh::lean_ctor_set(v___x_3088_, 0, v___x_3090_);
                    v___x_3092_ = v___x_3088_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
                    v___x_3092_ = v_reuseFailAlloc_3093_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(
    mut v_preNode_3096_: *mut crate::leanh::LeanObject,
    mut v_postNode_3097_: *mut crate::leanh::LeanObject,
    mut v___x_3098_: *mut crate::leanh::LeanObject,
    mut v_x_3099_: *mut crate::leanh::LeanObject,
    mut v_x_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3099_) == 0 {
                    crate::leanh::lean_dec(v___x_3098_);
                    crate::leanh::lean_dec_ref(v_postNode_3097_);
                    crate::leanh::lean_dec_ref(v_preNode_3096_);
                    v___x_3104_ = l_List_reverse___redArg(v_x_3100_);
                    v___x_3105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3105_, 0, v___x_3104_);
                    return v___x_3105_;
                } else {
                    v_head_3106_ = crate::leanh::lean_ctor_get(v_x_3099_, 0);
                    v_tail_3107_ = crate::leanh::lean_ctor_get(v_x_3099_, 1);
                    v_isSharedCheck_3125_ = (!crate::leanh::lean_is_exclusive(v_x_3099_)) as u8;
                    if v_isSharedCheck_3125_ == 0 {
                        v___x_3109_ = v_x_3099_;
                        v_isShared_3110_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3107_);
                        crate::leanh::lean_inc(v_head_3106_);
                        crate::leanh::lean_dec(v_x_3099_);
                        v___x_3109_ = crate::leanh::lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_3098_);
                crate::leanh::lean_inc_ref(v_postNode_3097_);
                crate::leanh::lean_inc_ref(v_preNode_3096_);
                v___x_3111_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3096_, v_postNode_3097_, v___x_3098_, v_head_3106_, v___y_3101_, v___y_3102_);
                if crate::leanh::lean_obj_tag(v___x_3111_) == 0 {
                    v_a_3112_ = crate::leanh::lean_ctor_get(v___x_3111_, 0);
                    crate::leanh::lean_inc(v_a_3112_);
                    crate::leanh::lean_dec_ref_known(v___x_3111_, 1);
                    if v_isShared_3110_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3109_, 1, v_x_3100_);
                        crate::leanh::lean_ctor_set(v___x_3109_, 0, v_a_3112_);
                        v___x_3114_ = v___x_3109_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3116_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3112_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_x_3100_);
                        v___x_3114_ = v_reuseFailAlloc_3116_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3109_);
                    crate::leanh::lean_dec(v_tail_3107_);
                    crate::leanh::lean_dec(v_x_3100_);
                    crate::leanh::lean_dec(v___x_3098_);
                    crate::leanh::lean_dec_ref(v_postNode_3097_);
                    crate::leanh::lean_dec_ref(v_preNode_3096_);
                    v_a_3117_ = crate::leanh::lean_ctor_get(v___x_3111_, 0);
                    v_isSharedCheck_3124_ = (!crate::leanh::lean_is_exclusive(v___x_3111_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3119_ = v___x_3111_;
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3117_);
                        crate::leanh::lean_dec(v___x_3111_);
                        v___x_3119_ = crate::leanh::lean_box(0);
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3099_ = v_tail_3107_;
                v_x_3100_ = v___x_3114_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(
    mut v_preNode_3126_: *mut crate::leanh::LeanObject,
    mut v_postNode_3127_: *mut crate::leanh::LeanObject,
    mut v___x_3128_: *mut crate::leanh::LeanObject,
    mut v_x_3129_: *mut crate::leanh::LeanObject,
    mut v_x_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3134_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3126_, v_postNode_3127_, v___x_3128_, v_x_3129_, v_x_3130_, v___y_3131_, v___y_3132_);
    crate::leanh::lean_dec(v___y_3132_);
    crate::leanh::lean_dec_ref(v___y_3131_);
    return v_res_3134_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(
    mut v_preNode_3135_: *mut crate::leanh::LeanObject,
    mut v_postNode_3136_: *mut crate::leanh::LeanObject,
    mut v_x_3137_: *mut crate::leanh::LeanObject,
    mut v_x_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3142_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3135_, v_postNode_3136_, v_x_3137_, v_x_3138_, v___y_3139_, v___y_3140_);
    crate::leanh::lean_dec(v___y_3140_);
    crate::leanh::lean_dec_ref(v___y_3139_);
    return v_res_3142_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
    mut v_preNode_3143_: *mut crate::leanh::LeanObject,
    mut v_postNode_3144_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_3145_: *mut crate::leanh::LeanObject,
    mut v_t_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_unused_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3150_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3150_, 0, v_postNode_3144_);
                v___x_3151_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3143_, v___f_3150_, v_ctx_x3f_3145_, v_t_3146_, v___y_3147_, v___y_3148_);
                if crate::leanh::lean_obj_tag(v___x_3151_) == 0 {
                    v_isSharedCheck_3159_ = (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3159_ == 0 {
                        v_unused_3160_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                        crate::leanh::lean_dec(v_unused_3160_);
                        v___x_3153_ = v___x_3151_;
                        v_isShared_3154_ = v_isSharedCheck_3159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3151_);
                        v___x_3153_ = crate::leanh::lean_box(0);
                        v_isShared_3154_ = v_isSharedCheck_3159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3161_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3168_ = (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3163_ = v___x_3151_;
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3161_);
                        crate::leanh::lean_dec(v___x_3151_);
                        v___x_3163_ = crate::leanh::lean_box(0);
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3155_ = crate::leanh::lean_box(0);
                if v_isShared_3154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3155_);
                    v___x_3157_ = v___x_3153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3157_;
            }
            3 => {
                if v_isShared_3164_ == 0 {
                    v___x_3166_ = v___x_3163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
                    v___x_3166_ = v_reuseFailAlloc_3167_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(
    mut v_preNode_3169_: *mut crate::leanh::LeanObject,
    mut v_postNode_3170_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_3171_: *mut crate::leanh::LeanObject,
    mut v_t_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
        v_preNode_3169_,
        v_postNode_3170_,
        v_ctx_x3f_3171_,
        v_t_3172_,
        v___y_3173_,
        v___y_3174_,
    );
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    return v_res_3176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(
    mut v___x_3177_: u8,
    mut v_x_3178_: *mut crate::leanh::LeanObject,
    mut v_x_3179_: *mut crate::leanh::LeanObject,
    mut v_x_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ = crate::leanh::lean_box((v___x_3177_) as usize);
    v___x_3185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3185_, 0, v___x_3184_);
    return v___x_3185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(
    mut v___x_3186_: *mut crate::leanh::LeanObject,
    mut v_x_3187_: *mut crate::leanh::LeanObject,
    mut v_x_3188_: *mut crate::leanh::LeanObject,
    mut v_x_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15366__boxed_3193_: u8 = 0;
    let mut v_res_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15366__boxed_3193_ = (crate::leanh::lean_unbox(v___x_3186_) as u8);
    v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_15366__boxed_3193_, v_x_3187_, v_x_3188_, v_x_3189_, v___y_3190_, v___y_3191_);
    crate::leanh::lean_dec(v___y_3191_);
    crate::leanh::lean_dec_ref(v___y_3190_);
    crate::leanh::lean_dec_ref(v_x_3189_);
    crate::leanh::lean_dec_ref(v_x_3188_);
    crate::leanh::lean_dec_ref(v_x_3187_);
    return v_res_3194_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(
    mut v___x_3195_: u8,
    mut v_val_3196_: *mut crate::leanh::LeanObject,
    mut v_as_3197_: *mut crate::leanh::LeanObject,
    mut v_sz_3198_: usize,
    mut v_i_3199_: usize,
    mut v_b_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3204_ = lean_usize_dec_lt(v_i_3199_, v_sz_3198_);
                if v___x_3204_ == 0 {
                    crate::leanh::lean_dec(v_val_3196_);
                    v___x_3205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3205_, 0, v_b_3200_);
                    return v___x_3205_;
                } else {
                    v___x_3206_ = crate::leanh::lean_box((v___x_3195_) as usize);
                    v___f_3207_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_3207_, 0, v___x_3206_);
                    v___x_3208_ = crate::leanh::lean_box((v___x_3195_) as usize);
                    crate::leanh::lean_inc(v_val_3196_);
                    v___f_3209_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___f_3209_, 0, v_val_3196_);
                    crate::leanh::lean_closure_set(v___f_3209_, 1, v___x_3208_);
                    v_a_3210_ = lean_array_uget_borrowed(v_as_3197_, v_i_3199_);
                    v___x_3211_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_3210_);
                    v___x_3212_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
                            v___f_3207_,
                            v___f_3209_,
                            v___x_3211_,
                            v_a_3210_,
                            v___y_3201_,
                            v___y_3202_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3212_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3212_, 1);
                        v___x_3213_ = crate::leanh::lean_box(0);
                        v___x_3214_ = 1usize;
                        v___x_3215_ = lean_usize_add(v_i_3199_, v___x_3214_);
                        v_i_3199_ = v___x_3215_;
                        v_b_3200_ = v___x_3213_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_3196_);
                        return v___x_3212_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(
    mut v___x_3217_: *mut crate::leanh::LeanObject,
    mut v_val_3218_: *mut crate::leanh::LeanObject,
    mut v_as_3219_: *mut crate::leanh::LeanObject,
    mut v_sz_3220_: *mut crate::leanh::LeanObject,
    mut v_i_3221_: *mut crate::leanh::LeanObject,
    mut v_b_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15391__boxed_3226_: u8 = 0;
    let mut v_sz_boxed_3227_: usize = 0;
    let mut v_i_boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15391__boxed_3226_ = (crate::leanh::lean_unbox(v___x_3217_) as u8);
    v_sz_boxed_3227_ = crate::leanh::lean_unbox_usize(v_sz_3220_);
    crate::leanh::lean_dec(v_sz_3220_);
    v_i_boxed_3228_ = crate::leanh::lean_unbox_usize(v_i_3221_);
    crate::leanh::lean_dec(v_i_3221_);
    v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_15391__boxed_3226_, v_val_3218_, v_as_3219_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3222_, v___y_3223_, v___y_3224_);
    crate::leanh::lean_dec(v___y_3224_);
    crate::leanh::lean_dec_ref(v___y_3223_);
    crate::leanh::lean_dec_ref(v_as_3219_);
    return v_res_3229_;
}
pub unsafe fn _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = crate::leanh::lean_box(0);
    v___x_3231_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3232_ = lean_mk_array(v___x_3231_, v___x_3230_);
    return v___x_3232_;
}
pub unsafe fn _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_unusedSimpArgs___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once),
        _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0,
    );
    v___x_3234_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3235_, 0, v___x_3234_);
    crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3233_);
    return v___x_3235_;
}
pub unsafe fn l_Lean_Linter_unusedSimpArgs___lam__0(
    mut v_cmdStx_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3261_: usize = 0;
    let mut v___x_3262_: usize = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3267_: usize = 0;
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_unused_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___y_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v_size_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: u8 = 0;
    let mut v___x_3301_: u8 = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3240_ =
                    l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(
                        v___y_3237_,
                        v___y_3238_,
                    );
                v_a_3241_ = crate::leanh::lean_ctor_get(v___x_3240_, 0);
                v_isSharedCheck_3310_ = (!crate::leanh::lean_is_exclusive(v___x_3240_)) as u8;
                if v_isSharedCheck_3310_ == 0 {
                    v___x_3243_ = v___x_3240_;
                    v_isShared_3244_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3241_);
                    crate::leanh::lean_dec(v___x_3240_);
                    v___x_3243_ = crate::leanh::lean_box(0);
                    v_isShared_3244_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3245_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
                v___x_3246_ = l_Lean_Linter_getLinterValue(v___x_3245_, v_a_3241_);
                crate::leanh::lean_dec(v_a_3241_);
                if v___x_3246_ == 0 {
                    v___x_3247_ = crate::leanh::lean_box(0);
                    if v_isShared_3244_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3243_, 0, v___x_3247_);
                        v___x_3249_ = v___x_3243_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
                        v___x_3249_ = v_reuseFailAlloc_3250_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3251_ = 0;
                    v___x_3252_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_3236_, v___x_3251_);
                    if crate::leanh::lean_obj_tag(v___x_3252_) == 1 {
                        crate::leanh::lean_dec_ref_known(v___x_3252_, 1);
                        crate::leanh::lean_del_object(v___x_3243_);
                        v___x_3253_ = lean_st_ref_get(v___y_3238_);
                        v___x_3254_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3255_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_unusedSimpArgs___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1,
                        );
                        v___x_3256_ = lean_st_mk_ref(v___x_3255_);
                        v_infoState_3257_ = crate::leanh::lean_ctor_get(v___x_3253_, 8);
                        crate::leanh::lean_inc_ref(v_infoState_3257_);
                        crate::leanh::lean_dec(v___x_3253_);
                        v_trees_3258_ = crate::leanh::lean_ctor_get(v_infoState_3257_, 2);
                        crate::leanh::lean_inc_ref(v_trees_3258_);
                        crate::leanh::lean_dec_ref(v_infoState_3257_);
                        v___x_3259_ = l_Lean_PersistentArray_toArray___redArg(v_trees_3258_);
                        crate::leanh::lean_dec_ref(v_trees_3258_);
                        v___x_3260_ = crate::leanh::lean_box(0);
                        v_sz_3261_ = lean_array_size(v___x_3259_);
                        v___x_3262_ = 0usize;
                        crate::leanh::lean_inc(v___x_3256_);
                        v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_3246_, v___x_3256_, v___x_3259_, v_sz_3261_, v___x_3262_, v___x_3260_, v___y_3237_, v___y_3238_);
                        crate::leanh::lean_dec_ref(v___x_3259_);
                        if crate::leanh::lean_obj_tag(v___x_3263_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3263_, 1);
                            v___x_3264_ = lean_st_ref_get(v___x_3256_);
                            crate::leanh::lean_dec(v___x_3256_);
                            v_size_3296_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                            crate::leanh::lean_inc(v_size_3296_);
                            v_buckets_3297_ = crate::leanh::lean_ctor_get(v___x_3264_, 1);
                            crate::leanh::lean_inc_ref(v_buckets_3297_);
                            crate::leanh::lean_dec(v___x_3264_);
                            v___x_3298_ = lean_mk_empty_array_with_capacity(v_size_3296_);
                            crate::leanh::lean_dec(v_size_3296_);
                            v___x_3299_ = lean_array_get_size(v_buckets_3297_);
                            v___x_3300_ = lean_nat_dec_lt(v___x_3254_, v___x_3299_);
                            if v___x_3300_ == 0 {
                                crate::leanh::lean_dec_ref(v_buckets_3297_);
                                v___y_3290_ = v___x_3298_;
                                state = 8;
                                continue;
                            } else {
                                v___x_3301_ = lean_nat_dec_le(v___x_3299_, v___x_3299_);
                                if v___x_3301_ == 0 {
                                    if v___x_3300_ == 0 {
                                        crate::leanh::lean_dec_ref(v_buckets_3297_);
                                        v___y_3290_ = v___x_3298_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_3302_ = lean_usize_of_nat(v___x_3299_);
                                        v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_3297_, v___x_3262_, v___x_3302_, v___x_3298_);
                                        crate::leanh::lean_dec_ref(v_buckets_3297_);
                                        v___y_3290_ = v___x_3303_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v___x_3304_ = lean_usize_of_nat(v___x_3299_);
                                    v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_3297_, v___x_3262_, v___x_3304_, v___x_3298_);
                                    crate::leanh::lean_dec_ref(v_buckets_3297_);
                                    v___y_3290_ = v___x_3305_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3256_);
                            return v___x_3263_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3252_);
                        v___x_3306_ = crate::leanh::lean_box(0);
                        if v_isShared_3244_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3243_, 0, v___x_3306_);
                            v___x_3308_ = v___x_3243_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3309_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
                            v___x_3308_ = v_reuseFailAlloc_3309_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3249_;
            }
            3 => {
                v_sz_3267_ = lean_array_size(v___y_3266_);
                v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_3266_, v_sz_3267_, v___x_3262_, v___x_3260_, v___y_3237_, v___y_3238_);
                crate::leanh::lean_dec_ref(v___y_3266_);
                if crate::leanh::lean_obj_tag(v___x_3268_) == 0 {
                    v_isSharedCheck_3275_ = (!crate::leanh::lean_is_exclusive(v___x_3268_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v_unused_3276_ = crate::leanh::lean_ctor_get(v___x_3268_, 0);
                        crate::leanh::lean_dec(v_unused_3276_);
                        v___x_3270_ = v___x_3268_;
                        v_isShared_3271_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3268_);
                        v___x_3270_ = crate::leanh::lean_box(0);
                        v_isShared_3271_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_3268_;
                }
            }
            4 => {
                if v_isShared_3271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3260_);
                    v___x_3273_ = v___x_3270_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3260_);
                    v___x_3273_ = v_reuseFailAlloc_3274_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3273_;
            }
            6 => {
                v___x_3282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_3280_, v___y_3278_, v___y_3279_, v___y_3281_);
                crate::leanh::lean_dec(v___y_3281_);
                crate::leanh::lean_dec(v___y_3280_);
                v___y_3266_ = v___x_3282_;
                state = 3;
                continue;
            }
            7 => {
                v___x_3288_ = lean_nat_dec_le(v___y_3287_, v___y_3285_);
                if v___x_3288_ == 0 {
                    crate::leanh::lean_dec(v___y_3285_);
                    crate::leanh::lean_inc(v___y_3287_);
                    v___y_3278_ = v___y_3284_;
                    v___y_3279_ = v___y_3287_;
                    v___y_3280_ = v___y_3286_;
                    v___y_3281_ = v___y_3287_;
                    state = 6;
                    continue;
                } else {
                    v___y_3278_ = v___y_3284_;
                    v___y_3279_ = v___y_3287_;
                    v___y_3280_ = v___y_3286_;
                    v___y_3281_ = v___y_3285_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3291_ = lean_array_get_size(v___y_3290_);
                v___x_3292_ = lean_nat_dec_eq(v___x_3291_, v___x_3254_);
                if v___x_3292_ == 0 {
                    v___x_3293_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3294_ = lean_nat_sub(v___x_3291_, v___x_3293_);
                    v___x_3295_ = lean_nat_dec_le(v___x_3254_, v___x_3294_);
                    if v___x_3295_ == 0 {
                        crate::leanh::lean_inc(v___x_3294_);
                        v___y_3284_ = v___y_3290_;
                        v___y_3285_ = v___x_3294_;
                        v___y_3286_ = v___x_3291_;
                        v___y_3287_ = v___x_3294_;
                        state = 7;
                        continue;
                    } else {
                        v___y_3284_ = v___y_3290_;
                        v___y_3285_ = v___x_3294_;
                        v___y_3286_ = v___x_3291_;
                        v___y_3287_ = v___x_3254_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_3266_ = v___y_3290_;
                    state = 3;
                    continue;
                }
            }
            9 => {
                return v___x_3308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_unusedSimpArgs___lam__0___boxed(
    mut v_cmdStx_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_3311_, v___y_3312_, v___y_3313_);
    crate::leanh::lean_dec(v___y_3313_);
    crate::leanh::lean_dec_ref(v___y_3312_);
    crate::leanh::lean_dec(v_cmdStx_3311_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(
    mut v_o_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_3327_, v___y_3329_);
    return v___x_3331_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(
    mut v_o_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_3332_, v___y_3333_, v___y_3334_);
    crate::leanh::lean_dec(v___y_3334_);
    crate::leanh::lean_dec_ref(v___y_3333_);
    return v_res_3336_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(
    mut v_00_u03b2_3337_: *mut crate::leanh::LeanObject,
    mut v_m_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_b_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_3338_, v_a_3339_, v_b_3340_);
    return v___x_3341_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(
    mut v_00_u03b2_3342_: *mut crate::leanh::LeanObject,
    mut v_m_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_3343_, v_a_3344_);
    return v___x_3345_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(
    mut v_00_u03b2_3346_: *mut crate::leanh::LeanObject,
    mut v_m_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(
            v_00_u03b2_3346_,
            v_m_3347_,
            v_a_3348_,
        );
    crate::leanh::lean_dec_ref(v_a_3348_);
    crate::leanh::lean_dec_ref(v_m_3347_);
    return v_res_3349_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(
    mut v_00_u03b1_3350_: *mut crate::leanh::LeanObject,
    mut v_ref_3351_: *mut crate::leanh::LeanObject,
    mut v_msg_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
        v_ref_3351_,
        v_msg_3352_,
        v___y_3353_,
        v___y_3354_,
    );
    return v___x_3356_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(
    mut v_00_u03b1_3357_: *mut crate::leanh::LeanObject,
    mut v_ref_3358_: *mut crate::leanh::LeanObject,
    mut v_msg_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(
        v_00_u03b1_3357_,
        v_ref_3358_,
        v_msg_3359_,
        v___y_3360_,
        v___y_3361_,
    );
    crate::leanh::lean_dec(v___y_3361_);
    crate::leanh::lean_dec_ref(v___y_3360_);
    crate::leanh::lean_dec(v_ref_3358_);
    return v_res_3363_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(
    mut v_upperBound_3364_: *mut crate::leanh::LeanObject,
    mut v_snd_3365_: *mut crate::leanh::LeanObject,
    mut v_fst_3366_: *mut crate::leanh::LeanObject,
    mut v_inst_3367_: *mut crate::leanh::LeanObject,
    mut v_R_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_b_3370_: *mut crate::leanh::LeanObject,
    mut v_c_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3375_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(
            v_upperBound_3364_,
            v_snd_3365_,
            v_fst_3366_,
            v_a_3369_,
            v_b_3370_,
            v___y_3372_,
            v___y_3373_,
        );
    return v___x_3375_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(
    mut v_upperBound_3376_: *mut crate::leanh::LeanObject,
    mut v_snd_3377_: *mut crate::leanh::LeanObject,
    mut v_fst_3378_: *mut crate::leanh::LeanObject,
    mut v_inst_3379_: *mut crate::leanh::LeanObject,
    mut v_R_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_b_3382_: *mut crate::leanh::LeanObject,
    mut v_c_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(
        v_upperBound_3376_,
        v_snd_3377_,
        v_fst_3378_,
        v_inst_3379_,
        v_R_3380_,
        v_a_3381_,
        v_b_3382_,
        v_c_3383_,
        v___y_3384_,
        v___y_3385_,
    );
    crate::leanh::lean_dec(v___y_3385_);
    crate::leanh::lean_dec_ref(v___y_3384_);
    crate::leanh::lean_dec_ref(v_snd_3377_);
    crate::leanh::lean_dec(v_upperBound_3376_);
    return v_res_3387_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(
    mut v_n_3388_: *mut crate::leanh::LeanObject,
    mut v_as_3389_: *mut crate::leanh::LeanObject,
    mut v_lo_3390_: *mut crate::leanh::LeanObject,
    mut v_hi_3391_: *mut crate::leanh::LeanObject,
    mut v_w_3392_: *mut crate::leanh::LeanObject,
    mut v_hlo_3393_: *mut crate::leanh::LeanObject,
    mut v_hhi_3394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_3388_, v_as_3389_, v_lo_3390_, v_hi_3391_);
    return v___x_3395_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(
    mut v_n_3396_: *mut crate::leanh::LeanObject,
    mut v_as_3397_: *mut crate::leanh::LeanObject,
    mut v_lo_3398_: *mut crate::leanh::LeanObject,
    mut v_hi_3399_: *mut crate::leanh::LeanObject,
    mut v_w_3400_: *mut crate::leanh::LeanObject,
    mut v_hlo_3401_: *mut crate::leanh::LeanObject,
    mut v_hhi_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_3396_, v_as_3397_, v_lo_3398_, v_hi_3399_, v_w_3400_, v_hlo_3401_, v_hhi_3402_);
    crate::leanh::lean_dec(v_hi_3399_);
    crate::leanh::lean_dec(v_n_3396_);
    return v_res_3403_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(
    mut v_00_u03b2_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
    mut v_x_3406_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3407_: u8 = 0;
    v___x_3407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_3405_, v_x_3406_);
    return v___x_3407_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(
    mut v_00_u03b2_3408_: *mut crate::leanh::LeanObject,
    mut v_a_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3411_: u8 = 0;
    let mut v_r_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_3408_, v_a_3409_, v_x_3410_);
    crate::leanh::lean_dec(v_x_3410_);
    crate::leanh::lean_dec_ref(v_a_3409_);
    v_r_3412_ = crate::leanh::lean_box((v_res_3411_) as usize);
    return v_r_3412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(
    mut v_00_u03b2_3413_: *mut crate::leanh::LeanObject,
    mut v_data_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(
    mut v_00_u03b2_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_b_3418_: *mut crate::leanh::LeanObject,
    mut v_x_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_3417_, v_b_3418_, v_x_3419_);
    return v___x_3420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(
    mut v_00_u03b2_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_x_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_3422_, v_x_3423_);
    return v___x_3424_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(
    mut v_00_u03b2_3425_: *mut crate::leanh::LeanObject,
    mut v_a_3426_: *mut crate::leanh::LeanObject,
    mut v_x_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_3425_, v_a_3426_, v_x_3427_);
    crate::leanh::lean_dec(v_x_3427_);
    crate::leanh::lean_dec_ref(v_a_3426_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(
    mut v_msgData_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_3429_, v___y_3431_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(
    mut v_msgData_3434_: *mut crate::leanh::LeanObject,
    mut v___y_3435_: *mut crate::leanh::LeanObject,
    mut v___y_3436_: *mut crate::leanh::LeanObject,
    mut v___y_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_3434_, v___y_3435_, v___y_3436_);
    crate::leanh::lean_dec(v___y_3436_);
    crate::leanh::lean_dec_ref(v___y_3435_);
    return v_res_3438_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(
    mut v_00_u03b1_3439_: *mut crate::leanh::LeanObject,
    mut v_msg_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_3440_, v___y_3441_, v___y_3442_);
    return v___x_3444_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(
    mut v_00_u03b1_3445_: *mut crate::leanh::LeanObject,
    mut v_msg_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
    mut v___y_3448_: *mut crate::leanh::LeanObject,
    mut v___y_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_3445_, v_msg_3446_, v___y_3447_, v___y_3448_);
    crate::leanh::lean_dec(v___y_3448_);
    crate::leanh::lean_dec_ref(v___y_3447_);
    return v_res_3450_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(
    mut v_00_u03b1_3451_: *mut crate::leanh::LeanObject,
    mut v_msg_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_3452_, v___y_3453_, v___y_3454_);
    return v___x_3456_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(
    mut v_00_u03b1_3457_: *mut crate::leanh::LeanObject,
    mut v_msg_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_3457_, v_msg_3458_, v___y_3459_, v___y_3460_);
    crate::leanh::lean_dec(v___y_3460_);
    crate::leanh::lean_dec_ref(v___y_3459_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(
    mut v_00_u03b1_3463_: *mut crate::leanh::LeanObject,
    mut v_preNode_3464_: *mut crate::leanh::LeanObject,
    mut v_postNode_3465_: *mut crate::leanh::LeanObject,
    mut v_x_3466_: *mut crate::leanh::LeanObject,
    mut v_x_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3464_, v_postNode_3465_, v_x_3466_, v_x_3467_, v___y_3468_, v___y_3469_);
    return v___x_3471_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(
    mut v_00_u03b1_3472_: *mut crate::leanh::LeanObject,
    mut v_preNode_3473_: *mut crate::leanh::LeanObject,
    mut v_postNode_3474_: *mut crate::leanh::LeanObject,
    mut v_x_3475_: *mut crate::leanh::LeanObject,
    mut v_x_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_3472_, v_preNode_3473_, v_postNode_3474_, v_x_3475_, v_x_3476_, v___y_3477_, v___y_3478_);
    crate::leanh::lean_dec(v___y_3478_);
    crate::leanh::lean_dec_ref(v___y_3477_);
    return v_res_3480_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(
    mut v_n_3481_: *mut crate::leanh::LeanObject,
    mut v_lo_3482_: *mut crate::leanh::LeanObject,
    mut v_hi_3483_: *mut crate::leanh::LeanObject,
    mut v_hhi_3484_: *mut crate::leanh::LeanObject,
    mut v_pivot_3485_: *mut crate::leanh::LeanObject,
    mut v_as_3486_: *mut crate::leanh::LeanObject,
    mut v_i_3487_: *mut crate::leanh::LeanObject,
    mut v_k_3488_: *mut crate::leanh::LeanObject,
    mut v_ilo_3489_: *mut crate::leanh::LeanObject,
    mut v_ik_3490_: *mut crate::leanh::LeanObject,
    mut v_w_3491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_3483_, v_pivot_3485_, v_as_3486_, v_i_3487_, v_k_3488_);
    return v___x_3492_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(
    mut v_n_3493_: *mut crate::leanh::LeanObject,
    mut v_lo_3494_: *mut crate::leanh::LeanObject,
    mut v_hi_3495_: *mut crate::leanh::LeanObject,
    mut v_hhi_3496_: *mut crate::leanh::LeanObject,
    mut v_pivot_3497_: *mut crate::leanh::LeanObject,
    mut v_as_3498_: *mut crate::leanh::LeanObject,
    mut v_i_3499_: *mut crate::leanh::LeanObject,
    mut v_k_3500_: *mut crate::leanh::LeanObject,
    mut v_ilo_3501_: *mut crate::leanh::LeanObject,
    mut v_ik_3502_: *mut crate::leanh::LeanObject,
    mut v_w_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_3493_, v_lo_3494_, v_hi_3495_, v_hhi_3496_, v_pivot_3497_, v_as_3498_, v_i_3499_, v_k_3500_, v_ilo_3501_, v_ik_3502_, v_w_3503_);
    crate::leanh::lean_dec_ref(v_pivot_3497_);
    crate::leanh::lean_dec(v_hi_3495_);
    crate::leanh::lean_dec(v_lo_3494_);
    crate::leanh::lean_dec(v_n_3493_);
    return v_res_3504_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3505_: *mut crate::leanh::LeanObject,
    mut v_i_3506_: *mut crate::leanh::LeanObject,
    mut v_source_3507_: *mut crate::leanh::LeanObject,
    mut v_target_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3509_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_3506_, v_source_3507_, v_target_3508_);
    return v___x_3509_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(
    mut v_msgData_3510_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_3510_, v_macroStack_3511_, v___y_3513_);
    return v___x_3515_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(
    mut v_msgData_3516_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_3516_, v_macroStack_3517_, v___y_3518_, v___y_3519_);
    crate::leanh::lean_dec(v___y_3519_);
    crate::leanh::lean_dec_ref(v___y_3518_);
    return v_res_3521_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(
    mut v_00_u03b1_3522_: *mut crate::leanh::LeanObject,
    mut v_preNode_3523_: *mut crate::leanh::LeanObject,
    mut v_postNode_3524_: *mut crate::leanh::LeanObject,
    mut v___x_3525_: *mut crate::leanh::LeanObject,
    mut v_x_3526_: *mut crate::leanh::LeanObject,
    mut v_x_3527_: *mut crate::leanh::LeanObject,
    mut v___y_3528_: *mut crate::leanh::LeanObject,
    mut v___y_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3523_, v_postNode_3524_, v___x_3525_, v_x_3526_, v_x_3527_, v___y_3528_, v___y_3529_);
    return v___x_3531_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(
    mut v_00_u03b1_3532_: *mut crate::leanh::LeanObject,
    mut v_preNode_3533_: *mut crate::leanh::LeanObject,
    mut v_postNode_3534_: *mut crate::leanh::LeanObject,
    mut v___x_3535_: *mut crate::leanh::LeanObject,
    mut v_x_3536_: *mut crate::leanh::LeanObject,
    mut v_x_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_3532_, v_preNode_3533_, v_postNode_3534_, v___x_3535_, v_x_3536_, v_x_3537_, v___y_3538_, v___y_3539_);
    crate::leanh::lean_dec(v___y_3539_);
    crate::leanh::lean_dec_ref(v___y_3538_);
    return v_res_3541_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(
    mut v_00_u03b2_3542_: *mut crate::leanh::LeanObject,
    mut v_x_3543_: *mut crate::leanh::LeanObject,
    mut v_x_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_3543_, v_x_3544_);
    return v___x_3545_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_Linter_unusedSimpArgs;
    v___x_3548_ = l_Lean_Elab_Command_addLinter(v___x_3547_);
    return v___x_3548_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(
    mut v_a_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
    return v_res_3550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_UnusedSimpArgs(
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
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_UnusedSimpArgs(
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
pub unsafe fn initialize_Lean_Linter_UnusedSimpArgs(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_UnusedSimpArgs(builtin);
}
