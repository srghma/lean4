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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value
        ) as *mut LeanObject,
        16145843736367156323 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value
) as *mut LeanObject;
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value) as *mut LeanObject,7383208167966365478 as *mut LeanObject] };
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value:
    LeanStringObject<260> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value
) as *mut LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value
) as *mut LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value:
    LeanStringObject<38> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value
) as *mut LeanObject;
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [83, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 109, 97, 115, 107, 32, 115, 105, 122, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 125, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 118, 115, 46, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 65, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value) as *mut LeanObject,17985617252278808837 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value) as *mut LeanObject,12783917532758215986 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_unusedSimpArgs___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_unusedSimpArgs___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_unusedSimpArgs___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_unusedSimpArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_unusedSimpArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__2_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_unusedSimpArgs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__2_value) as *mut LeanObject;
static l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__1_value) as *mut LeanObject,
        8071394701935581384 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_unusedSimpArgs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__2_value) as *mut LeanObject,
        14321273934322160490 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_unusedSimpArgs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter_unusedSimpArgs___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_unusedSimpArgs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Linter_unusedSimpArgs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_unusedSimpArgs___closed__4_value) as *mut LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(
    mut v_upperBound_1776_: *mut LeanObject,
    mut v_i_1777_: *mut LeanObject,
    mut v_simpArgs_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_b_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1787_ = lean_nat_dec_lt(v_a_1779_, v_upperBound_1776_);
                if v___x_1787_ == 0 {
                    lean_dec(v_a_1779_);
                    v___x_1788_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1788_, 0, v_b_1780_);
                    return v___x_1788_;
                } else {
                    v___x_1789_ = lean_nat_dec_eq(v_a_1779_, v_i_1777_);
                    if v___x_1789_ == 0 {
                        v___x_1790_ = lean_array_fget_borrowed(v_simpArgs_1778_, v_a_1779_);
                        lean_inc(v___x_1790_);
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
                v___x_1784_ = lean_unsigned_to_nat(1);
                v___x_1785_ = lean_nat_add(v_a_1779_, v___x_1784_);
                lean_dec(v_a_1779_);
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
    mut v_upperBound_1792_: *mut LeanObject,
    mut v_i_1793_: *mut LeanObject,
    mut v_simpArgs_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_b_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_1792_, v_i_1793_, v_simpArgs_1794_, v_a_1795_, v_b_1796_);
    lean_dec_ref(v_simpArgs_1794_);
    lean_dec(v_i_1793_);
    lean_dec(v_upperBound_1792_);
    return v_res_1798_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    v___x_1799_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1799_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    v___x_1800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0);
    v___x_1801_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    v___x_1802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
    v___x_1803_ = lean_unsigned_to_nat(0);
    v___x_1804_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1804_, 0, v___x_1803_);
    lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    lean_ctor_set(v___x_1804_, 3, v___x_1803_);
    lean_ctor_set(v___x_1804_, 4, v___x_1802_);
    lean_ctor_set(v___x_1804_, 5, v___x_1802_);
    lean_ctor_set(v___x_1804_, 6, v___x_1802_);
    lean_ctor_set(v___x_1804_, 7, v___x_1802_);
    lean_ctor_set(v___x_1804_, 8, v___x_1802_);
    lean_ctor_set(v___x_1804_, 9, v___x_1802_);
    return v___x_1804_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    v___x_1805_ = lean_unsigned_to_nat(32);
    v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
    v___x_1807_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1807_, 0, v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4()
-> *mut LeanObject {
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    v___x_1808_ = 5usize;
    v___x_1809_ = lean_unsigned_to_nat(0);
    v___x_1810_ = lean_unsigned_to_nat(32);
    v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
    v___x_1812_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3);
    v___x_1813_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    lean_ctor_set(v___x_1813_, 2, v___x_1809_);
    lean_ctor_set(v___x_1813_, 3, v___x_1809_);
    lean_ctor_set_usize(v___x_1813_, 4, v___x_1808_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5()
-> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ = lean_box(1);
    v___x_1815_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4);
    v___x_1816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
    v___x_1817_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    lean_ctor_set(v___x_1817_, 1, v___x_1815_);
    lean_ctor_set(v___x_1817_, 2, v___x_1814_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(
    mut v_msgData_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_st_ref_get(v___y_1820_);
    v_env_1823_ = lean_ctor_get(v___x_1822_, 0);
    lean_inc_ref(v_env_1823_);
    lean_dec(v___x_1822_);
    v_options_1824_ = lean_ctor_get(v___y_1819_, 2);
    v___x_1825_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
    v___x_1826_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
    lean_inc_ref(v_options_1824_);
    v___x_1827_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1827_, 0, v_env_1823_);
    lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    lean_ctor_set(v___x_1827_, 2, v___x_1826_);
    lean_ctor_set(v___x_1827_, 3, v_options_1824_);
    v___x_1828_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1828_, 0, v___x_1827_);
    lean_ctor_set(v___x_1828_, 1, v_msgData_1818_);
    v___x_1829_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1829_, 0, v___x_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(
    mut v_msgData_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_1830_, v___y_1831_, v___y_1832_);
    lean_dec(v___y_1832_);
    lean_dec_ref(v___y_1831_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(
    mut v_msg_1835_: *mut LeanObject,
    mut v___y_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1839_ = lean_ctor_get(v___y_1836_, 5);
                v___x_1840_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_1835_, v___y_1836_, v___y_1837_);
                v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
                v_isSharedCheck_1849_ = (!lean_is_exclusive(v___x_1840_)) as u8;
                if v_isSharedCheck_1849_ == 0 {
                    v___x_1843_ = v___x_1840_;
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1841_);
                    lean_dec(v___x_1840_);
                    v___x_1843_ = lean_box(0);
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1839_);
                v___x_1845_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1845_, 0, v_ref_1839_);
                lean_ctor_set(v___x_1845_, 1, v_a_1841_);
                if v_isShared_1844_ == 0 {
                    lean_ctor_set_tag(v___x_1843_, 1);
                    lean_ctor_set(v___x_1843_, 0, v___x_1845_);
                    v___x_1847_ = v___x_1843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
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
    mut v_msg_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1854_: *mut LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_1850_, v___y_1851_, v___y_1852_);
    lean_dec(v___y_1852_);
    lean_dec_ref(v___y_1851_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(
    mut v___y_1863_: u8,
    mut v_suppressElabErrors_1864_: u8,
    mut v_x_1865_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1865_) == 1 {
        let mut v_pre_1866_: *mut LeanObject = core::ptr::null_mut();
        v_pre_1866_ = lean_ctor_get(v_x_1865_, 0);
        match lean_obj_tag(v_pre_1866_) {
            1 => {
                let mut v_pre_1867_: *mut LeanObject = core::ptr::null_mut();
                v_pre_1867_ = lean_ctor_get(v_pre_1866_, 0);
                match lean_obj_tag(v_pre_1867_) {
                    0 => {
                        let mut v_str_1868_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_1869_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1871_: u8 = 0;
                        v_str_1868_ = lean_ctor_get(v_x_1865_, 1);
                        v_str_1869_ = lean_ctor_get(v_pre_1866_, 1);
                        v___x_1870_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_1871_ = lean_string_dec_eq(v_str_1869_, v___x_1870_);
                        if v___x_1871_ == 0 {
                            let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1873_: u8 = 0;
                            v___x_1872_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_1873_ = lean_string_dec_eq(v_str_1869_, v___x_1872_);
                            if v___x_1873_ == 0 {
                                return v___y_1863_;
                            } else {
                                let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_1878_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_1878_ = lean_ctor_get(v_pre_1867_, 0);
                        if lean_obj_tag(v_pre_1878_) == 0 {
                            let mut v_str_1879_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_1880_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_1881_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1883_: u8 = 0;
                            v_str_1879_ = lean_ctor_get(v_x_1865_, 1);
                            v_str_1880_ = lean_ctor_get(v_pre_1866_, 1);
                            v_str_1881_ = lean_ctor_get(v_pre_1867_, 1);
                            v___x_1882_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_1883_ = lean_string_dec_eq(v_str_1881_, v___x_1882_);
                            if v___x_1883_ == 0 {
                                return v___y_1863_;
                            } else {
                                let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_1885_: u8 = 0;
                                v___x_1884_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_1885_ = lean_string_dec_eq(v_str_1880_, v___x_1884_);
                                if v___x_1885_ == 0 {
                                    return v___y_1863_;
                                } else {
                                    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_1888_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1890_: u8 = 0;
                v_str_1888_ = lean_ctor_get(v_x_1865_, 1);
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
    mut v___y_1891_: *mut LeanObject,
    mut v_suppressElabErrors_1892_: *mut LeanObject,
    mut v_x_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4604__boxed_1894_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1895_: u8 = 0;
    let mut v_res_1896_: u8 = 0;
    let mut v_r_1897_: *mut LeanObject = core::ptr::null_mut();
    v___y_4604__boxed_1894_ = (lean_unbox(v___y_1891_) as u8);
    v_suppressElabErrors_boxed_1895_ = (lean_unbox(v_suppressElabErrors_1892_) as u8);
    v_res_1896_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v___y_4604__boxed_1894_, v_suppressElabErrors_boxed_1895_, v_x_1893_);
    lean_dec(v_x_1893_);
    v_r_1897_ = lean_box((v_res_1896_) as usize);
    return v_r_1897_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(
    mut v_opts_1898_: *mut LeanObject,
    mut v_opt_1899_: *mut LeanObject,
) -> u8 {
    let mut v_name_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    v_name_1900_ = lean_ctor_get(v_opt_1899_, 0);
    v_defValue_1901_ = lean_ctor_get(v_opt_1899_, 1);
    v_map_1902_ = lean_ctor_get(v_opts_1898_, 0);
    v___x_1903_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1902_,
            v_name_1900_,
        );
    if lean_obj_tag(v___x_1903_) == 0 {
        let mut v___x_1904_: u8 = 0;
        v___x_1904_ = (lean_unbox(v_defValue_1901_) as u8);
        return v___x_1904_;
    } else {
        let mut v_val_1905_: *mut LeanObject = core::ptr::null_mut();
        v_val_1905_ = lean_ctor_get(v___x_1903_, 0);
        lean_inc(v_val_1905_);
        lean_dec_ref_known(v___x_1903_, 1);
        if lean_obj_tag(v_val_1905_) == 1 {
            let mut v_v_1906_: u8 = 0;
            v_v_1906_ = lean_ctor_get_uint8(v_val_1905_, 0 as u32);
            lean_dec_ref_known(v_val_1905_, 0);
            return v_v_1906_;
        } else {
            let mut v___x_1907_: u8 = 0;
            lean_dec(v_val_1905_);
            v___x_1907_ = (lean_unbox(v_defValue_1901_) as u8);
            return v___x_1907_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_opts_1908_: *mut LeanObject,
    mut v_opt_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1910_: u8 = 0;
    let mut v_r_1911_: *mut LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_1908_, v_opt_1909_);
    lean_dec_ref(v_opt_1909_);
    lean_dec_ref(v_opts_1908_);
    v_r_1911_ = lean_box((v_res_1910_) as usize);
    return v_r_1911_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(
    mut v_ref_1913_: *mut LeanObject,
    mut v_msgData_1914_: *mut LeanObject,
    mut v_severity_1915_: u8,
    mut v_isSilent_1916_: u8,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: u8 = 0;
    let mut v___y_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: u8 = 0;
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v___y_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1959_: u8 = 0;
    let mut v___y_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: u8 = 0;
    let mut v___y_1962_: u8 = 0;
    let mut v___y_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v___y_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: u8 = 0;
    let mut v___y_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: u8 = 0;
    let mut v___y_1988_: u8 = 0;
    let mut v___y_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: u8 = 0;
    let mut v___y_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: u8 = 0;
    let mut v___y_1999_: u8 = 0;
    let mut v_ref_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___y_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: u8 = 0;
    let mut v___y_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: u8 = 0;
    let mut v___y_2012_: u8 = 0;
    let mut v___y_2014_: u8 = 0;
    let mut v_fileName_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_1914_);
                    v___x_2030_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1914_);
                    v___y_2014_ = v___x_2030_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1930_ = lean_st_ref_take(v___y_1929_);
                v_currNamespace_1931_ = lean_ctor_get(v___y_1928_, 6);
                v_openDecls_1932_ = lean_ctor_get(v___y_1928_, 7);
                v_env_1933_ = lean_ctor_get(v___x_1930_, 0);
                v_nextMacroScope_1934_ = lean_ctor_get(v___x_1930_, 1);
                v_ngen_1935_ = lean_ctor_get(v___x_1930_, 2);
                v_auxDeclNGen_1936_ = lean_ctor_get(v___x_1930_, 3);
                v_traceState_1937_ = lean_ctor_get(v___x_1930_, 4);
                v_cache_1938_ = lean_ctor_get(v___x_1930_, 5);
                v_messages_1939_ = lean_ctor_get(v___x_1930_, 6);
                v_infoState_1940_ = lean_ctor_get(v___x_1930_, 7);
                v_snapshotTasks_1941_ = lean_ctor_get(v___x_1930_, 8);
                v_isSharedCheck_1955_ = (!lean_is_exclusive(v___x_1930_)) as u8;
                if v_isSharedCheck_1955_ == 0 {
                    v___x_1943_ = v___x_1930_;
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1941_);
                    lean_inc(v_infoState_1940_);
                    lean_inc(v_messages_1939_);
                    lean_inc(v_cache_1938_);
                    lean_inc(v_traceState_1937_);
                    lean_inc(v_auxDeclNGen_1936_);
                    lean_inc(v_ngen_1935_);
                    lean_inc(v_nextMacroScope_1934_);
                    lean_inc(v_env_1933_);
                    lean_dec(v___x_1930_);
                    v___x_1943_ = lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_1932_);
                lean_inc(v_currNamespace_1931_);
                v___x_1945_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1945_, 0, v_currNamespace_1931_);
                lean_ctor_set(v___x_1945_, 1, v_openDecls_1932_);
                v___x_1946_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1946_, 0, v___x_1945_);
                lean_ctor_set(v___x_1946_, 1, v___y_1925_);
                lean_inc_ref(v___y_1926_);
                lean_inc_ref(v___y_1923_);
                v___x_1947_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_1947_, 0, v___y_1923_);
                lean_ctor_set(v___x_1947_, 1, v___y_1922_);
                lean_ctor_set(v___x_1947_, 2, v___y_1921_);
                lean_ctor_set(v___x_1947_, 3, v___y_1926_);
                lean_ctor_set(v___x_1947_, 4, v___x_1946_);
                lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_1927_,
                );
                lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_1924_,
                );
                lean_ctor_set_uint8(
                    v___x_1947_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1916_,
                );
                v___x_1948_ = l_Lean_MessageLog_add(v___x_1947_, v_messages_1939_);
                if v_isShared_1944_ == 0 {
                    lean_ctor_set(v___x_1943_, 6, v___x_1948_);
                    v___x_1950_ = v___x_1943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_env_1933_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_nextMacroScope_1934_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_ngen_1935_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_auxDeclNGen_1936_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_traceState_1937_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 5, v_cache_1938_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 6, v___x_1948_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 7, v_infoState_1940_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 8, v_snapshotTasks_1941_);
                    v___x_1950_ = v_reuseFailAlloc_1954_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1951_ = lean_st_ref_set(v___y_1929_, v___x_1950_);
                v___x_1952_ = lean_box(0);
                v___x_1953_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1953_, 0, v___x_1952_);
                return v___x_1953_;
            }
            4 => {
                v___x_1965_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1914_,
                    );
                v___x_1966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_1965_, v___y_1917_, v___y_1918_);
                v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
                v_isSharedCheck_1980_ = (!lean_is_exclusive(v___x_1966_)) as u8;
                if v_isSharedCheck_1980_ == 0 {
                    v___x_1969_ = v___x_1966_;
                    v_isShared_1970_ = v_isSharedCheck_1980_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_1967_);
                    lean_dec(v___x_1966_);
                    v___x_1969_ = lean_box(0);
                    v_isShared_1970_ = v_isSharedCheck_1980_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_1958_, 2);
                v___x_1971_ = l_Lean_FileMap_toPosition(v___y_1958_, v___y_1963_);
                lean_dec(v___y_1963_);
                v___x_1972_ = l_Lean_FileMap_toPosition(v___y_1958_, v___y_1964_);
                lean_dec(v___y_1964_);
                v___x_1973_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1973_, 0, v___x_1972_);
                v___x_1974_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0;
                if v___y_1959_ == 0 {
                    lean_del_object(v___x_1969_);
                    lean_dec_ref(v___y_1957_);
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
                    lean_inc(v_a_1967_);
                    v___x_1975_ = l_Lean_MessageData_hasTag(v___y_1957_, v_a_1967_);
                    if v___x_1975_ == 0 {
                        lean_dec_ref_known(v___x_1973_, 1);
                        lean_dec_ref(v___x_1971_);
                        lean_dec(v_a_1967_);
                        v___x_1976_ = lean_box(0);
                        if v_isShared_1970_ == 0 {
                            lean_ctor_set(v___x_1969_, 0, v___x_1976_);
                            v___x_1978_ = v___x_1969_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
                            v___x_1978_ = v_reuseFailAlloc_1979_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1969_);
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
                lean_dec(v___y_1983_);
                if lean_obj_tag(v___x_1990_) == 0 {
                    lean_inc(v___y_1989_);
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
                    v_val_1991_ = lean_ctor_get(v___x_1990_, 0);
                    lean_inc(v_val_1991_);
                    lean_dec_ref_known(v___x_1990_, 1);
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
                if lean_obj_tag(v___x_2001_) == 0 {
                    v___x_2002_ = lean_unsigned_to_nat(0);
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
                    v_val_2003_ = lean_ctor_get(v___x_2001_, 0);
                    lean_inc(v_val_2003_);
                    lean_dec_ref_known(v___x_2001_, 1);
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
                    v_fileName_2015_ = lean_ctor_get(v___y_1917_, 0);
                    v_fileMap_2016_ = lean_ctor_get(v___y_1917_, 1);
                    v_options_2017_ = lean_ctor_get(v___y_1917_, 2);
                    v_ref_2018_ = lean_ctor_get(v___y_1917_, 5);
                    v_suppressElabErrors_2019_ = lean_ctor_get_uint8(
                        v___y_1917_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2020_ = lean_box((v___y_2014_) as usize);
                    v___x_2021_ = lean_box((v_suppressElabErrors_2019_) as usize);
                    v___f_2022_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2022_, 0, v___x_2020_);
                    lean_closure_set(v___f_2022_, 1, v___x_2021_);
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
                    lean_dec_ref(v_msgData_1914_);
                    v___x_2027_ = lean_box(0);
                    v___x_2028_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2028_, 0, v___x_2027_);
                    return v___x_2028_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(
    mut v_ref_2031_: *mut LeanObject,
    mut v_msgData_2032_: *mut LeanObject,
    mut v_severity_2033_: *mut LeanObject,
    mut v_isSilent_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2038_: u8 = 0;
    let mut v_isSilent_boxed_2039_: u8 = 0;
    let mut v_res_2040_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2038_ = (lean_unbox(v_severity_2033_) as u8);
    v_isSilent_boxed_2039_ = (lean_unbox(v_isSilent_2034_) as u8);
    v_res_2040_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_2031_, v_msgData_2032_, v_severity_boxed_2038_, v_isSilent_boxed_2039_, v___y_2035_, v___y_2036_);
    lean_dec(v___y_2036_);
    lean_dec_ref(v___y_2035_);
    lean_dec(v_ref_2031_);
    return v_res_2040_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(
    mut v_ref_2041_: *mut LeanObject,
    mut v_msgData_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    v___x_2046_ = 1;
    v___x_2047_ = 0;
    v___x_2048_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_2041_, v_msgData_2042_, v___x_2046_, v___x_2047_, v___y_2043_, v___y_2044_);
    return v___x_2048_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(
    mut v_ref_2049_: *mut LeanObject,
    mut v_msgData_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2054_: *mut LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_2049_, v_msgData_2050_, v___y_2051_, v___y_2052_);
    lean_dec(v___y_2052_);
    lean_dec_ref(v___y_2051_);
    lean_dec(v_ref_2049_);
    return v_res_2054_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    v___x_2056_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0;
    v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2;
    v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
    return v___x_2060_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(
    mut v_linterOption_2061_: *mut LeanObject,
    mut v_stx_2062_: *mut LeanObject,
    mut v_msg_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2067_ = lean_ctor_get(v_linterOption_2061_, 0);
                v_isSharedCheck_2084_ = (!lean_is_exclusive(v_linterOption_2061_)) as u8;
                if v_isSharedCheck_2084_ == 0 {
                    v_unused_2085_ = lean_ctor_get(v_linterOption_2061_, 1);
                    lean_dec(v_unused_2085_);
                    v___x_2069_ = v_linterOption_2061_;
                    v_isShared_2070_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2067_);
                    lean_dec(v_linterOption_2061_);
                    v___x_2069_ = lean_box(0);
                    v_isShared_2070_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2071_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
                lean_inc(v_name_2067_);
                v___x_2072_ = l_Lean_MessageData_ofName(v_name_2067_);
                if v_isShared_2070_ == 0 {
                    lean_ctor_set_tag(v___x_2069_, 7);
                    lean_ctor_set(v___x_2069_, 1, v___x_2072_);
                    lean_ctor_set(v___x_2069_, 0, v___x_2071_);
                    v___x_2074_ = v___x_2069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2071_);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2072_);
                    v___x_2074_ = v_reuseFailAlloc_2083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2075_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
                v___x_2076_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2076_, 0, v___x_2074_);
                lean_ctor_set(v___x_2076_, 1, v___x_2075_);
                v_disable_2077_ = l_Lean_MessageData_note(v___x_2076_);
                v___x_2078_ = l_Lean_Linter_linterMessageTag;
                v___x_2079_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2079_, 0, v_msg_2063_);
                lean_ctor_set(v___x_2079_, 1, v_disable_2077_);
                v___x_2080_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2080_, 0, v___x_2078_);
                lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                v___x_2081_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2081_, 0, v_name_2067_);
                lean_ctor_set(v___x_2081_, 1, v___x_2080_);
                v___x_2082_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_2062_, v___x_2081_, v___y_2064_, v___y_2065_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(
    mut v_linterOption_2086_: *mut LeanObject,
    mut v_stx_2087_: *mut LeanObject,
    mut v_msg_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2092_: *mut LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_2086_, v_stx_2087_, v_msg_2088_, v___y_2089_, v___y_2090_);
    lean_dec(v___y_2090_);
    lean_dec_ref(v___y_2089_);
    lean_dec(v_stx_2087_);
    return v_res_2092_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5()
-> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4;
    v___x_2102_ = l_Lean_MessageData_ofFormat(v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7()
-> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6;
    v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13()
-> *mut LeanObject {
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    v___x_2115_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12;
    v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
    return v___x_2116_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14()
-> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    v___x_2120_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15;
    v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
    return v___x_2121_;
}
pub unsafe fn _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18()
-> *mut LeanObject {
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    v___x_2123_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17;
    v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(
    mut v_stx_2125_: *mut LeanObject,
    mut v_i_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hint_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpArgs_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argStx_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_otherArgs_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_a_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = lean_box(0);
                v___x_2140_ =
                    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1;
                v_simpArgs_2141_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_2125_);
                v___x_2192_ = lean_array_get_size(v_simpArgs_2141_);
                v___x_2193_ = lean_nat_dec_lt(v_i_2126_, v___x_2192_);
                if v___x_2193_ == 0 {
                    lean_dec_ref(v_simpArgs_2141_);
                    v___x_2194_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
                    v___x_2195_ = l_Nat_reprFast(v_i_2126_);
                    v___x_2196_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2196_, 0, v___x_2195_);
                    v___x_2197_ = l_Lean_MessageData_ofFormat(v___x_2196_);
                    v___x_2198_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2198_, 0, v___x_2194_);
                    lean_ctor_set(v___x_2198_, 1, v___x_2197_);
                    v___x_2199_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
                    v___x_2200_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2200_, 0, v___x_2198_);
                    lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                    v___x_2201_ = l_Lean_MessageData_ofSyntax(v_stx_2125_);
                    v___x_2202_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2202_, 0, v___x_2200_);
                    lean_ctor_set(v___x_2202_, 1, v___x_2201_);
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
                v___x_2137_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2137_, 0, v___y_2131_);
                lean_ctor_set(v___x_2137_, 1, v_hint_2133_);
                v___x_2138_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_2136_, v___y_2132_, v___x_2137_, v___y_2134_, v___y_2135_);
                lean_dec(v___y_2132_);
                return v___x_2138_;
            }
            2 => {
                v___x_2145_ = lean_array_get_size(v_simpArgs_2141_);
                v___x_2146_ = lean_unsigned_to_nat(0);
                v_argStx_2147_ = lean_array_get(v___x_2139_, v_simpArgs_2141_, v_i_2126_);
                v_otherArgs_2148_ =
                    l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2;
                v___x_2149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_2145_, v_i_2126_, v_simpArgs_2141_, v___x_2146_, v_otherArgs_2148_);
                lean_dec_ref(v_simpArgs_2141_);
                lean_dec(v_i_2126_);
                if lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
                    lean_inc(v_a_2150_);
                    lean_dec_ref_known(v___x_2149_, 1);
                    lean_inc(v_stx_2125_);
                    v___x_2151_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_2125_, v_a_2150_);
                    lean_dec(v_a_2150_);
                    v___x_2152_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2152_, 0, v___x_2140_);
                    lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                    v___x_2153_ = lean_box(0);
                    v___x_2154_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v___x_2154_, 0, v___x_2152_);
                    lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                    lean_ctor_set(v___x_2154_, 2, v___x_2153_);
                    lean_ctor_set(v___x_2154_, 3, v___x_2153_);
                    lean_ctor_set(v___x_2154_, 4, v___x_2153_);
                    lean_ctor_set(v___x_2154_, 5, v___x_2153_);
                    v___x_2155_ = 0;
                    v___x_2156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2156_, 0, v_stx_2125_);
                    v___x_2157_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v___x_2157_, 0, v___x_2154_);
                    lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                    lean_ctor_set(v___x_2157_, 2, v___x_2153_);
                    lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_2155_,
                    );
                    v___x_2158_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5);
                    v___x_2159_ = lean_unsigned_to_nat(1);
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
                    lean_dec_ref(v___x_2161_);
                    if lean_obj_tag(v___x_2163_) == 0 {
                        v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
                        lean_inc(v_a_2164_);
                        lean_dec_ref_known(v___x_2163_, 1);
                        v___x_2165_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
                        lean_inc_n(v_argStx_2147_, 2);
                        v___x_2166_ = l_Lean_MessageData_ofSyntax(v_argStx_2147_);
                        v___x_2167_ = l_Lean_indentD(v___x_2166_);
                        v_msg_2168_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_msg_2168_, 0, v___x_2165_);
                        lean_ctor_set(v_msg_2168_, 1, v___x_2167_);
                        v___x_2169_ = l_Lean_Syntax_getKind(v_argStx_2147_);
                        v___x_2170_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11;
                        v___x_2171_ = lean_name_eq(v___x_2169_, v___x_2170_);
                        lean_dec(v___x_2169_);
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
                            lean_dec(v___x_2172_);
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
                                    v___x_2174_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once), _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
                                    v___x_2175_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_2175_, 0, v_a_2164_);
                                    lean_ctor_set(v___x_2175_, 1, v___x_2174_);
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
                        lean_dec(v_argStx_2147_);
                        v_a_2176_ = lean_ctor_get(v___x_2163_, 0);
                        v_isSharedCheck_2183_ = (!lean_is_exclusive(v___x_2163_)) as u8;
                        if v_isSharedCheck_2183_ == 0 {
                            v___x_2178_ = v___x_2163_;
                            v_isShared_2179_ = v_isSharedCheck_2183_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2176_);
                            lean_dec(v___x_2163_);
                            v___x_2178_ = lean_box(0);
                            v_isShared_2179_ = v_isSharedCheck_2183_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_argStx_2147_);
                    lean_dec(v_stx_2125_);
                    v_a_2184_ = lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2191_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2186_ = v___x_2149_;
                        v_isShared_2187_ = v_isSharedCheck_2191_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2184_);
                        lean_dec(v___x_2149_);
                        v___x_2186_ = lean_box(0);
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
                    v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
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
                    v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
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
    mut v_stx_2204_: *mut LeanObject,
    mut v_i_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2209_: *mut LeanObject = core::ptr::null_mut();
    v_res_2209_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(
        v_stx_2204_,
        v_i_2205_,
        v_a_2206_,
        v_a_2207_,
    );
    lean_dec(v_a_2207_);
    lean_dec_ref(v_a_2206_);
    return v_res_2209_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(
    mut v_upperBound_2210_: *mut LeanObject,
    mut v_i_2211_: *mut LeanObject,
    mut v_simpArgs_2212_: *mut LeanObject,
    mut v_inst_2213_: *mut LeanObject,
    mut v_R_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_b_2216_: *mut LeanObject,
    mut v_c_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_2210_, v_i_2211_, v_simpArgs_2212_, v_a_2215_, v_b_2216_);
    return v___x_2221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(
    mut v_upperBound_2222_: *mut LeanObject,
    mut v_i_2223_: *mut LeanObject,
    mut v_simpArgs_2224_: *mut LeanObject,
    mut v_inst_2225_: *mut LeanObject,
    mut v_R_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
    mut v_b_2228_: *mut LeanObject,
    mut v_c_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2233_: *mut LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_2222_, v_i_2223_, v_simpArgs_2224_, v_inst_2225_, v_R_2226_, v_a_2227_, v_b_2228_, v_c_2229_, v___y_2230_, v___y_2231_);
    lean_dec(v___y_2231_);
    lean_dec_ref(v___y_2230_);
    lean_dec_ref(v_simpArgs_2224_);
    lean_dec(v_i_2223_);
    lean_dec(v_upperBound_2222_);
    return v_res_2233_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(
    mut v_00_u03b1_2234_: *mut LeanObject,
    mut v_msg_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_2235_, v___y_2236_, v___y_2237_);
    return v___x_2239_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(
    mut v_00_u03b1_2240_: *mut LeanObject,
    mut v_msg_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2245_: *mut LeanObject = core::ptr::null_mut();
    v_res_2245_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_2240_, v_msg_2241_, v___y_2242_, v___y_2243_);
    lean_dec(v___y_2243_);
    lean_dec_ref(v___y_2242_);
    return v_res_2245_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(
    mut v_upperBound_2246_: *mut LeanObject,
    mut v_snd_2247_: *mut LeanObject,
    mut v_fst_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
    mut v_b_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2259_ = lean_nat_dec_lt(v_a_2249_, v_upperBound_2246_);
                if v___x_2259_ == 0 {
                    lean_dec(v_a_2249_);
                    lean_dec(v_fst_2248_);
                    v___x_2260_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2260_, 0, v_b_2250_);
                    return v___x_2260_;
                } else {
                    v___x_2261_ = lean_box(0);
                    v___x_2262_ = 0;
                    v___x_2263_ = lean_box((v___x_2262_) as usize);
                    v___x_2264_ = lean_array_get(v___x_2263_, v_snd_2247_, v_a_2249_);
                    lean_dec(v___x_2263_);
                    v___x_2265_ = (lean_unbox(v___x_2264_) as u8);
                    lean_dec(v___x_2264_);
                    if v___x_2265_ == 0 {
                        lean_inc(v_a_2249_);
                        lean_inc(v_fst_2248_);
                        v___x_2266_ = lean_alloc_closure(
                            l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed
                                as *mut core::ffi::c_void,
                            5,
                            2,
                        );
                        lean_closure_set(v___x_2266_, 0, v_fst_2248_);
                        lean_closure_set(v___x_2266_, 1, v_a_2249_);
                        v___x_2267_ = l_Lean_Elab_Command_liftCoreM___redArg(
                            v___x_2266_,
                            v___y_2251_,
                            v___y_2252_,
                        );
                        if lean_obj_tag(v___x_2267_) == 0 {
                            lean_dec_ref_known(v___x_2267_, 1);
                            v_a_2255_ = v___x_2261_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2249_);
                            lean_dec(v_fst_2248_);
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
                v___x_2256_ = lean_unsigned_to_nat(1);
                v___x_2257_ = lean_nat_add(v_a_2249_, v___x_2256_);
                lean_dec(v_a_2249_);
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
    mut v_upperBound_2268_: *mut LeanObject,
    mut v_snd_2269_: *mut LeanObject,
    mut v_fst_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_b_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2274_);
    lean_dec_ref(v___y_2273_);
    lean_dec_ref(v_snd_2269_);
    lean_dec(v_upperBound_2268_);
    return v_res_2276_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(
    mut v_as_2277_: *mut LeanObject,
    mut v_sz_2278_: usize,
    mut v_i_2279_: usize,
    mut v_b_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2284_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
                if v___x_2284_ == 0 {
                    v___x_2285_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2285_, 0, v_b_2280_);
                    return v___x_2285_;
                } else {
                    v_a_2286_ = lean_array_uget_borrowed(v_as_2277_, v_i_2279_);
                    v_snd_2287_ = lean_ctor_get(v_a_2286_, 1);
                    v_fst_2288_ = lean_ctor_get(v_snd_2287_, 0);
                    v_snd_2289_ = lean_ctor_get(v_snd_2287_, 1);
                    v___x_2290_ = lean_box(0);
                    v___x_2291_ = lean_array_get_size(v_snd_2289_);
                    v___x_2292_ = lean_unsigned_to_nat(0);
                    lean_inc(v_fst_2288_);
                    v___x_2293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_2291_, v_snd_2289_, v_fst_2288_, v___x_2292_, v___x_2290_, v___y_2281_, v___y_2282_);
                    if lean_obj_tag(v___x_2293_) == 0 {
                        lean_dec_ref_known(v___x_2293_, 1);
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
    mut v_as_2297_: *mut LeanObject,
    mut v_sz_2298_: *mut LeanObject,
    mut v_i_2299_: *mut LeanObject,
    mut v_b_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2304_: usize = 0;
    let mut v_i_boxed_2305_: usize = 0;
    let mut v_res_2306_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2304_ = lean_unbox_usize(v_sz_2298_);
    lean_dec(v_sz_2298_);
    v_i_boxed_2305_ = lean_unbox_usize(v_i_2299_);
    lean_dec(v_i_2299_);
    v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_2297_, v_sz_boxed_2304_, v_i_boxed_2305_, v_b_2300_, v___y_2301_, v___y_2302_);
    lean_dec(v___y_2302_);
    lean_dec_ref(v___y_2301_);
    lean_dec_ref(v_as_2297_);
    return v_res_2306_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(
    mut v_hi_2307_: *mut LeanObject,
    mut v_pivot_2308_: *mut LeanObject,
    mut v_as_2309_: *mut LeanObject,
    mut v_i_2310_: *mut LeanObject,
    mut v_k_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2312_ = lean_nat_dec_lt(v_k_2311_, v_hi_2307_);
                if v___x_2312_ == 0 {
                    lean_dec(v_k_2311_);
                    v___x_2313_ = lean_array_fswap(v_as_2309_, v_i_2310_, v_hi_2307_);
                    v___x_2314_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2314_, 0, v_i_2310_);
                    lean_ctor_set(v___x_2314_, 1, v___x_2313_);
                    return v___x_2314_;
                } else {
                    v___x_2315_ = lean_array_fget_borrowed(v_as_2309_, v_k_2311_);
                    v_fst_2316_ = lean_ctor_get(v___x_2315_, 0);
                    v_fst_2317_ = lean_ctor_get(v_pivot_2308_, 0);
                    v_start_2318_ = lean_ctor_get(v_fst_2316_, 0);
                    v_start_2319_ = lean_ctor_get(v_fst_2317_, 0);
                    v___x_2320_ = lean_nat_dec_lt(v_start_2318_, v_start_2319_);
                    if v___x_2320_ == 0 {
                        v___x_2321_ = lean_unsigned_to_nat(1);
                        v___x_2322_ = lean_nat_add(v_k_2311_, v___x_2321_);
                        lean_dec(v_k_2311_);
                        v_k_2311_ = v___x_2322_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2324_ = lean_array_fswap(v_as_2309_, v_i_2310_, v_k_2311_);
                        v___x_2325_ = lean_unsigned_to_nat(1);
                        v___x_2326_ = lean_nat_add(v_i_2310_, v___x_2325_);
                        lean_dec(v_i_2310_);
                        v___x_2327_ = lean_nat_add(v_k_2311_, v___x_2325_);
                        lean_dec(v_k_2311_);
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
    mut v_hi_2329_: *mut LeanObject,
    mut v_pivot_2330_: *mut LeanObject,
    mut v_as_2331_: *mut LeanObject,
    mut v_i_2332_: *mut LeanObject,
    mut v_k_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2334_: *mut LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_2329_, v_pivot_2330_, v_as_2331_, v_i_2332_, v_k_2333_);
    lean_dec_ref(v_pivot_2330_);
    lean_dec(v_hi_2329_);
    return v_res_2334_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(
    mut v_x1_2335_: *mut LeanObject,
    mut v_x2_2336_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: u8 = 0;
    v_fst_2337_ = lean_ctor_get(v_x1_2335_, 0);
    v_fst_2338_ = lean_ctor_get(v_x2_2336_, 0);
    v_start_2339_ = lean_ctor_get(v_fst_2337_, 0);
    v_start_2340_ = lean_ctor_get(v_fst_2338_, 0);
    v___x_2341_ = lean_nat_dec_lt(v_start_2339_, v_start_2340_);
    return v___x_2341_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(
    mut v_x1_2342_: *mut LeanObject,
    mut v_x2_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2344_: u8 = 0;
    let mut v_r_2345_: *mut LeanObject = core::ptr::null_mut();
    v_res_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_2342_, v_x2_2343_);
    lean_dec_ref(v_x2_2343_);
    lean_dec_ref(v_x1_2342_);
    v_r_2345_ = lean_box((v_res_2344_) as usize);
    return v_r_2345_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(
    mut v_n_2346_: *mut LeanObject,
    mut v_as_2347_: *mut LeanObject,
    mut v_lo_2348_: *mut LeanObject,
    mut v_hi_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2361_ = lean_nat_dec_lt(v_lo_2348_, v_hi_2349_);
                if v___x_2361_ == 0 {
                    lean_dec(v_lo_2348_);
                    return v_as_2347_;
                } else {
                    v___x_2362_ = lean_nat_add(v_lo_2348_, v_hi_2349_);
                    v___x_2363_ = lean_unsigned_to_nat(1);
                    v_mid_2364_ = lean_nat_shiftr(v___x_2362_, v___x_2363_);
                    lean_dec(v___x_2362_);
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
                lean_inc_n(v_lo_2348_, 2);
                v___x_2353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_2349_, v_pivot_2352_, v___y_2351_, v_lo_2348_, v_lo_2348_);
                lean_dec(v_pivot_2352_);
                v_fst_2354_ = lean_ctor_get(v___x_2353_, 0);
                lean_inc(v_fst_2354_);
                v_snd_2355_ = lean_ctor_get(v___x_2353_, 1);
                lean_inc(v_snd_2355_);
                lean_dec_ref(v___x_2353_);
                v___x_2356_ = lean_nat_dec_le(v_hi_2349_, v_fst_2354_);
                if v___x_2356_ == 0 {
                    v___x_2357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_2346_, v_snd_2355_, v_lo_2348_, v_fst_2354_);
                    v___x_2358_ = lean_unsigned_to_nat(1);
                    v___x_2359_ = lean_nat_add(v_fst_2354_, v___x_2358_);
                    lean_dec(v_fst_2354_);
                    v_as_2347_ = v___x_2357_;
                    v_lo_2348_ = v___x_2359_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2354_);
                    lean_dec(v_lo_2348_);
                    return v_snd_2355_;
                }
            }
            2 => {
                v___x_2367_ = lean_array_fget_borrowed(v___y_2366_, v_mid_2364_);
                v___x_2368_ = lean_array_fget_borrowed(v___y_2366_, v_hi_2349_);
                v___x_2369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_2367_, v___x_2368_);
                if v___x_2369_ == 0 {
                    lean_dec(v_mid_2364_);
                    v___y_2351_ = v___y_2366_;
                    state = 1;
                    continue;
                } else {
                    v___x_2370_ = lean_array_fswap(v___y_2366_, v_mid_2364_, v_hi_2349_);
                    lean_dec(v_mid_2364_);
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
    mut v_n_2381_: *mut LeanObject,
    mut v_as_2382_: *mut LeanObject,
    mut v_lo_2383_: *mut LeanObject,
    mut v_hi_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2385_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_2381_, v_as_2382_, v_lo_2383_, v_hi_2384_);
    lean_dec(v_hi_2384_);
    lean_dec(v_n_2381_);
    return v_res_2385_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(
    mut v_x_2386_: *mut LeanObject,
    mut v_x_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2387_) == 0 {
                    return v_x_2386_;
                } else {
                    v_key_2388_ = lean_ctor_get(v_x_2387_, 0);
                    v_value_2389_ = lean_ctor_get(v_x_2387_, 1);
                    v_tail_2390_ = lean_ctor_get(v_x_2387_, 2);
                    lean_inc(v_value_2389_);
                    lean_inc(v_key_2388_);
                    v___x_2391_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2391_, 0, v_key_2388_);
                    lean_ctor_set(v___x_2391_, 1, v_value_2389_);
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
    mut v_x_2394_: *mut LeanObject,
    mut v_x_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2396_: *mut LeanObject = core::ptr::null_mut();
    v_res_2396_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(
            v_x_2394_, v_x_2395_,
        );
    lean_dec(v_x_2395_);
    return v_res_2396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(
    mut v_as_2397_: *mut LeanObject,
    mut v_i_2398_: usize,
    mut v_stop_2399_: usize,
    mut v_b_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_2407_: *mut LeanObject,
    mut v_i_2408_: *mut LeanObject,
    mut v_stop_2409_: *mut LeanObject,
    mut v_b_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2411_: usize = 0;
    let mut v_stop_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2411_ = lean_unbox_usize(v_i_2408_);
    lean_dec(v_i_2408_);
    v_stop_boxed_2412_ = lean_unbox_usize(v_stop_2409_);
    lean_dec(v_stop_2409_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_2407_, v_i_boxed_2411_, v_stop_boxed_2412_, v_b_2410_);
    lean_dec_ref(v_as_2407_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(
    mut v_o_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    v___x_2417_ = lean_st_ref_get(v___y_2415_);
    v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
    lean_inc_ref(v_env_2418_);
    lean_dec(v___x_2417_);
    v___x_2419_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2420_ = lean_ctor_get(v___x_2419_, 0);
    v_asyncMode_2421_ = lean_ctor_get(v_toEnvExtension_2420_, 2);
    v___x_2422_ = lean_box(1);
    v___x_2423_ = lean_box(0);
    v_linterSets_2424_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2422_,
        v___x_2419_,
        v_env_2418_,
        v_asyncMode_2421_,
        v___x_2423_,
    );
    v___x_2425_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2425_, 0, v_o_2414_);
    lean_ctor_set(v___x_2425_, 1, v_linterSets_2424_);
    v___x_2426_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2426_, 0, v___x_2425_);
    return v___x_2426_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(
    mut v_o_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2430_: *mut LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_2427_, v___y_2428_);
    lean_dec(v___y_2428_);
    return v_res_2430_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2434_ = lean_st_ref_get(v___y_2432_);
    v_scopes_2435_ = lean_ctor_get(v___x_2434_, 2);
    lean_inc(v_scopes_2435_);
    lean_dec(v___x_2434_);
    v___x_2436_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2437_ = l_List_head_x21___redArg(v___x_2436_, v_scopes_2435_);
    lean_dec(v_scopes_2435_);
    v_opts_2438_ = lean_ctor_get(v___x_2437_, 1);
    lean_inc_ref(v_opts_2438_);
    lean_dec(v___x_2437_);
    v___x_2439_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_2438_, v___y_2432_);
    return v___x_2439_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(
        v___y_2440_,
        v___y_2441_,
    );
    lean_dec(v___y_2441_);
    lean_dec_ref(v___y_2440_);
    return v_res_2443_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(
    mut v_a_2444_: *mut LeanObject,
    mut v_x_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2445_) == 0 {
                    v___x_2446_ = lean_box(0);
                    return v___x_2446_;
                } else {
                    v_key_2447_ = lean_ctor_get(v_x_2445_, 0);
                    v_value_2448_ = lean_ctor_get(v_x_2445_, 1);
                    v_tail_2449_ = lean_ctor_get(v_x_2445_, 2);
                    v___x_2450_ = l_Lean_Syntax_instBEqRange_beq(v_key_2447_, v_a_2444_);
                    if v___x_2450_ == 0 {
                        v_x_2445_ = v_tail_2449_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2448_);
                        v___x_2452_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2452_, 0, v_value_2448_);
                        return v___x_2452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(
    mut v_a_2453_: *mut LeanObject,
    mut v_x_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_2453_, v_x_2454_);
    lean_dec(v_x_2454_);
    lean_dec_ref(v_a_2453_);
    return v_res_2455_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(
    mut v_m_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2458_ = lean_ctor_get(v_m_2456_, 1);
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
    mut v_m_2474_: *mut LeanObject,
    mut v_a_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2476_: *mut LeanObject = core::ptr::null_mut();
    v_res_2476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_2474_, v_a_2475_);
    lean_dec_ref(v_a_2475_);
    lean_dec_ref(v_m_2474_);
    return v_res_2476_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
    mut v___x_2477_: u8,
    mut v_as_2478_: *mut LeanObject,
    mut v_bs_2479_: *mut LeanObject,
    mut v_i_2480_: *mut LeanObject,
    mut v_cs_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2483_: u8 = 0;
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v_a_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v_b_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2489_ = lean_array_get_size(v_as_2478_);
                v___x_2490_ = lean_nat_dec_lt(v_i_2480_, v___x_2489_);
                if v___x_2490_ == 0 {
                    lean_dec(v_i_2480_);
                    return v_cs_2481_;
                } else {
                    v___x_2491_ = lean_array_get_size(v_bs_2479_);
                    v___x_2492_ = lean_nat_dec_lt(v_i_2480_, v___x_2491_);
                    if v___x_2492_ == 0 {
                        lean_dec(v_i_2480_);
                        return v_cs_2481_;
                    } else {
                        v_a_2493_ = lean_array_fget_borrowed(v_as_2478_, v_i_2480_);
                        v___x_2494_ = (lean_unbox(v_a_2493_) as u8);
                        if v___x_2494_ == 0 {
                            v_b_2495_ = lean_array_fget_borrowed(v_bs_2479_, v_i_2480_);
                            v___x_2496_ = (lean_unbox(v_b_2495_) as u8);
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
                v___x_2484_ = lean_unsigned_to_nat(1);
                v___x_2485_ = lean_nat_add(v_i_2480_, v___x_2484_);
                lean_dec(v_i_2480_);
                v___x_2486_ = lean_box((v___y_2483_) as usize);
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
    mut v___x_2497_: *mut LeanObject,
    mut v_as_2498_: *mut LeanObject,
    mut v_bs_2499_: *mut LeanObject,
    mut v_i_2500_: *mut LeanObject,
    mut v_cs_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14147__boxed_2502_: u8 = 0;
    let mut v_res_2503_: *mut LeanObject = core::ptr::null_mut();
    v___x_14147__boxed_2502_ = (lean_unbox(v___x_2497_) as u8);
    v_res_2503_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
        v___x_14147__boxed_2502_,
        v_as_2498_,
        v_bs_2499_,
        v_i_2500_,
        v_cs_2501_,
    );
    lean_dec_ref(v_bs_2499_);
    lean_dec_ref(v_as_2498_);
    return v_res_2503_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(
    mut v_msgData_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    v___x_2507_ = lean_st_ref_get(v___y_2505_);
    v_env_2508_ = lean_ctor_get(v___x_2507_, 0);
    lean_inc_ref(v_env_2508_);
    lean_dec(v___x_2507_);
    v___x_2509_ = lean_st_ref_get(v___y_2505_);
    v_scopes_2510_ = lean_ctor_get(v___x_2509_, 2);
    lean_inc(v_scopes_2510_);
    lean_dec(v___x_2509_);
    v___x_2511_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2512_ = l_List_head_x21___redArg(v___x_2511_, v_scopes_2510_);
    lean_dec(v_scopes_2510_);
    v_opts_2513_ = lean_ctor_get(v___x_2512_, 1);
    lean_inc_ref(v_opts_2513_);
    lean_dec(v___x_2512_);
    v___x_2514_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
    v___x_2515_ = lean_unsigned_to_nat(32);
    v___x_2516_ = lean_mk_empty_array_with_capacity(v___x_2515_);
    lean_dec_ref(v___x_2516_);
    v___x_2517_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
    v___x_2518_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2518_, 0, v_env_2508_);
    lean_ctor_set(v___x_2518_, 1, v___x_2514_);
    lean_ctor_set(v___x_2518_, 2, v___x_2517_);
    lean_ctor_set(v___x_2518_, 3, v_opts_2513_);
    v___x_2519_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    lean_ctor_set(v___x_2519_, 1, v_msgData_2504_);
    v___x_2520_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2520_, 0, v___x_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(
    mut v_msgData_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2524_: *mut LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_2521_, v___y_2522_);
    lean_dec(v___y_2522_);
    return v_res_2524_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0()
-> *mut LeanObject {
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2525_ = lean_box(1);
    v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
    return v___x_2526_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3()
-> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2;
    v___x_2531_ = l_Lean_MessageData_ofFormat(v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(
    mut v_x_2532_: *mut LeanObject,
    mut v_x_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v_before_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_unused_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2533_) == 0 {
                    return v_x_2532_;
                } else {
                    v_head_2534_ = lean_ctor_get(v_x_2533_, 0);
                    v_tail_2535_ = lean_ctor_get(v_x_2533_, 1);
                    v_isSharedCheck_2557_ = (!lean_is_exclusive(v_x_2533_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v___x_2537_ = v_x_2533_;
                        v_isShared_2538_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2535_);
                        lean_inc(v_head_2534_);
                        lean_dec(v_x_2533_);
                        v___x_2537_ = lean_box(0);
                        v_isShared_2538_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2539_ = lean_ctor_get(v_head_2534_, 0);
                v_isSharedCheck_2555_ = (!lean_is_exclusive(v_head_2534_)) as u8;
                if v_isSharedCheck_2555_ == 0 {
                    v_unused_2556_ = lean_ctor_get(v_head_2534_, 1);
                    lean_dec(v_unused_2556_);
                    v___x_2541_ = v_head_2534_;
                    v_isShared_2542_ = v_isSharedCheck_2555_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_2539_);
                    lean_dec(v_head_2534_);
                    v___x_2541_ = lean_box(0);
                    v_isShared_2542_ = v_isSharedCheck_2555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2543_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
                if v_isShared_2542_ == 0 {
                    lean_ctor_set_tag(v___x_2541_, 7);
                    lean_ctor_set(v___x_2541_, 1, v___x_2543_);
                    lean_ctor_set(v___x_2541_, 0, v_x_2532_);
                    v___x_2545_ = v___x_2541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_x_2532_);
                    lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2543_);
                    v___x_2545_ = v_reuseFailAlloc_2554_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2546_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
                if v_isShared_2538_ == 0 {
                    lean_ctor_set_tag(v___x_2537_, 7);
                    lean_ctor_set(v___x_2537_, 1, v___x_2546_);
                    lean_ctor_set(v___x_2537_, 0, v___x_2545_);
                    v___x_2548_ = v___x_2537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2545_);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2546_);
                    v___x_2548_ = v_reuseFailAlloc_2553_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2549_ = l_Lean_MessageData_ofSyntax(v_before_2539_);
                v___x_2550_ = l_Lean_indentD(v___x_2549_);
                v___x_2551_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2551_, 0, v___x_2548_);
                lean_ctor_set(v___x_2551_, 1, v___x_2550_);
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
-> *mut LeanObject {
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    v___x_2561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1;
    v___x_2562_ = l_Lean_MessageData_ofFormat(v___x_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(
    mut v_msgData_2563_: *mut LeanObject,
    mut v_macroStack_2564_: *mut LeanObject,
    mut v___y_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v_unused_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2567_ = lean_st_ref_get(v___y_2565_);
                v_scopes_2568_ = lean_ctor_get(v___x_2567_, 2);
                lean_inc(v_scopes_2568_);
                lean_dec(v___x_2567_);
                v___x_2569_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2570_ = l_List_head_x21___redArg(v___x_2569_, v_scopes_2568_);
                lean_dec(v_scopes_2568_);
                v_opts_2571_ = lean_ctor_get(v___x_2570_, 1);
                lean_inc_ref(v_opts_2571_);
                lean_dec(v___x_2570_);
                v___x_2572_ = l_Lean_Elab_pp_macroStack;
                v___x_2573_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_2571_, v___x_2572_);
                lean_dec_ref(v_opts_2571_);
                if v___x_2573_ == 0 {
                    lean_dec(v_macroStack_2564_);
                    v___x_2574_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2574_, 0, v_msgData_2563_);
                    return v___x_2574_;
                } else {
                    if lean_obj_tag(v_macroStack_2564_) == 0 {
                        v___x_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2575_, 0, v_msgData_2563_);
                        return v___x_2575_;
                    } else {
                        v_head_2576_ = lean_ctor_get(v_macroStack_2564_, 0);
                        lean_inc(v_head_2576_);
                        v_after_2577_ = lean_ctor_get(v_head_2576_, 1);
                        v_isSharedCheck_2592_ = (!lean_is_exclusive(v_head_2576_)) as u8;
                        if v_isSharedCheck_2592_ == 0 {
                            v_unused_2593_ = lean_ctor_get(v_head_2576_, 0);
                            lean_dec(v_unused_2593_);
                            v___x_2579_ = v_head_2576_;
                            v_isShared_2580_ = v_isSharedCheck_2592_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_2577_);
                            lean_dec(v_head_2576_);
                            v___x_2579_ = lean_box(0);
                            v_isShared_2580_ = v_isSharedCheck_2592_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2581_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
                if v_isShared_2580_ == 0 {
                    lean_ctor_set_tag(v___x_2579_, 7);
                    lean_ctor_set(v___x_2579_, 1, v___x_2581_);
                    lean_ctor_set(v___x_2579_, 0, v_msgData_2563_);
                    v___x_2583_ = v___x_2579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_msgData_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2581_);
                    v___x_2583_ = v_reuseFailAlloc_2591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2584_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
                v___x_2585_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2585_, 0, v___x_2583_);
                lean_ctor_set(v___x_2585_, 1, v___x_2584_);
                v___x_2586_ = l_Lean_MessageData_ofSyntax(v_after_2577_);
                v___x_2587_ = l_Lean_indentD(v___x_2586_);
                v_msgData_2588_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_2588_, 0, v___x_2585_);
                lean_ctor_set(v_msgData_2588_, 1, v___x_2587_);
                v___x_2589_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_2588_, v_macroStack_2564_);
                v___x_2590_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2590_, 0, v___x_2589_);
                return v___x_2590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(
    mut v_msgData_2594_: *mut LeanObject,
    mut v_macroStack_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_2594_, v_macroStack_2595_, v___y_2596_);
    lean_dec(v___y_2596_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(
    mut v_msg_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut v_a_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2603_ = l_Lean_Elab_Command_getRef___redArg(v___y_2600_);
                if lean_obj_tag(v___x_2603_) == 0 {
                    v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
                    lean_inc(v_a_2604_);
                    lean_dec_ref_known(v___x_2603_, 1);
                    v_macroStack_2605_ = lean_ctor_get(v___y_2600_, 4);
                    v___x_2606_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_2599_, v___y_2601_);
                    v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
                    lean_inc(v_a_2607_);
                    lean_dec_ref(v___x_2606_);
                    v___x_2608_ = l_Lean_Elab_getBetterRef(v_a_2604_, v_macroStack_2605_);
                    lean_dec(v_a_2604_);
                    lean_inc(v_macroStack_2605_);
                    v___x_2609_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_2607_, v_macroStack_2605_, v___y_2601_);
                    v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2618_ = (!lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2618_ == 0 {
                        v___x_2612_ = v___x_2609_;
                        v_isShared_2613_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2610_);
                        lean_dec(v___x_2609_);
                        v___x_2612_ = lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_2599_);
                    v_a_2619_ = lean_ctor_get(v___x_2603_, 0);
                    v_isSharedCheck_2626_ = (!lean_is_exclusive(v___x_2603_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2621_ = v___x_2603_;
                        v_isShared_2622_ = v_isSharedCheck_2626_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2619_);
                        lean_dec(v___x_2603_);
                        v___x_2621_ = lean_box(0);
                        v_isShared_2622_ = v_isSharedCheck_2626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2614_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2614_, 0, v___x_2608_);
                lean_ctor_set(v___x_2614_, 1, v_a_2610_);
                if v_isShared_2613_ == 0 {
                    lean_ctor_set_tag(v___x_2612_, 1);
                    lean_ctor_set(v___x_2612_, 0, v___x_2614_);
                    v___x_2616_ = v___x_2612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
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
                    v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
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
    mut v_msg_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2631_: *mut LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_2627_, v___y_2628_, v___y_2629_);
    lean_dec(v___y_2629_);
    lean_dec_ref(v___y_2628_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
    mut v_ref_2632_: *mut LeanObject,
    mut v_msg_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2648_: u8 = 0;
    let mut v_ref_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2637_ = l_Lean_Elab_Command_getRef___redArg(v___y_2634_);
                if lean_obj_tag(v___x_2637_) == 0 {
                    v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
                    lean_inc(v_a_2638_);
                    lean_dec_ref_known(v___x_2637_, 1);
                    v_fileName_2639_ = lean_ctor_get(v___y_2634_, 0);
                    v_fileMap_2640_ = lean_ctor_get(v___y_2634_, 1);
                    v_currRecDepth_2641_ = lean_ctor_get(v___y_2634_, 2);
                    v_cmdPos_2642_ = lean_ctor_get(v___y_2634_, 3);
                    v_macroStack_2643_ = lean_ctor_get(v___y_2634_, 4);
                    v_quotContext_x3f_2644_ = lean_ctor_get(v___y_2634_, 5);
                    v_currMacroScope_2645_ = lean_ctor_get(v___y_2634_, 6);
                    v_snap_x3f_2646_ = lean_ctor_get(v___y_2634_, 8);
                    v_cancelTk_x3f_2647_ = lean_ctor_get(v___y_2634_, 9);
                    v_suppressElabErrors_2648_ = lean_ctor_get_uint8(
                        v___y_2634_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_2649_ = l_Lean_replaceRef(v_ref_2632_, v_a_2638_);
                    lean_dec(v_a_2638_);
                    lean_inc(v_cancelTk_x3f_2647_);
                    lean_inc(v_snap_x3f_2646_);
                    lean_inc(v_currMacroScope_2645_);
                    lean_inc(v_quotContext_x3f_2644_);
                    lean_inc(v_macroStack_2643_);
                    lean_inc(v_cmdPos_2642_);
                    lean_inc(v_currRecDepth_2641_);
                    lean_inc_ref(v_fileMap_2640_);
                    lean_inc_ref(v_fileName_2639_);
                    v___x_2650_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_2650_, 0, v_fileName_2639_);
                    lean_ctor_set(v___x_2650_, 1, v_fileMap_2640_);
                    lean_ctor_set(v___x_2650_, 2, v_currRecDepth_2641_);
                    lean_ctor_set(v___x_2650_, 3, v_cmdPos_2642_);
                    lean_ctor_set(v___x_2650_, 4, v_macroStack_2643_);
                    lean_ctor_set(v___x_2650_, 5, v_quotContext_x3f_2644_);
                    lean_ctor_set(v___x_2650_, 6, v_currMacroScope_2645_);
                    lean_ctor_set(v___x_2650_, 7, v_ref_2649_);
                    lean_ctor_set(v___x_2650_, 8, v_snap_x3f_2646_);
                    lean_ctor_set(v___x_2650_, 9, v_cancelTk_x3f_2647_);
                    lean_ctor_set_uint8(
                        v___x_2650_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2648_,
                    );
                    v___x_2651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_2633_, v___x_2650_, v___y_2635_);
                    lean_dec_ref_known(v___x_2650_, 10);
                    return v___x_2651_;
                } else {
                    lean_dec_ref(v_msg_2633_);
                    v_a_2652_ = lean_ctor_get(v___x_2637_, 0);
                    v_isSharedCheck_2659_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                    if v_isSharedCheck_2659_ == 0 {
                        v___x_2654_ = v___x_2637_;
                        v_isShared_2655_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2652_);
                        lean_dec(v___x_2637_);
                        v___x_2654_ = lean_box(0);
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
                    v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
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
    mut v_ref_2660_: *mut LeanObject,
    mut v_msg_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2665_: *mut LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
        v_ref_2660_,
        v_msg_2661_,
        v___y_2662_,
        v___y_2663_,
    );
    lean_dec(v___y_2663_);
    lean_dec_ref(v___y_2662_);
    lean_dec(v_ref_2660_);
    return v_res_2665_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(
    mut v_x_2666_: *mut LeanObject,
    mut v_x_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2667_) == 0 {
                    return v_x_2666_;
                } else {
                    v_key_2668_ = lean_ctor_get(v_x_2667_, 0);
                    v_value_2669_ = lean_ctor_get(v_x_2667_, 1);
                    v_tail_2670_ = lean_ctor_get(v_x_2667_, 2);
                    v_isSharedCheck_2693_ = (!lean_is_exclusive(v_x_2667_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2672_ = v_x_2667_;
                        v_isShared_2673_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2670_);
                        lean_inc(v_value_2669_);
                        lean_inc(v_key_2668_);
                        lean_dec(v_x_2667_);
                        v___x_2672_ = lean_box(0);
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
                lean_inc(v___x_2687_);
                if v_isShared_2673_ == 0 {
                    lean_ctor_set(v___x_2672_, 2, v___x_2687_);
                    v___x_2689_ = v___x_2672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_key_2668_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_value_2669_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2687_);
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
    mut v_i_2694_: *mut LeanObject,
    mut v_source_2695_: *mut LeanObject,
    mut v_target_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v_es_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2697_ = lean_array_get_size(v_source_2695_);
                v___x_2698_ = lean_nat_dec_lt(v_i_2694_, v___x_2697_);
                if v___x_2698_ == 0 {
                    lean_dec_ref(v_source_2695_);
                    lean_dec(v_i_2694_);
                    return v_target_2696_;
                } else {
                    v_es_2699_ = lean_array_fget(v_source_2695_, v_i_2694_);
                    v___x_2700_ = lean_box(0);
                    v_source_2701_ = lean_array_fset(v_source_2695_, v_i_2694_, v___x_2700_);
                    v_target_2702_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_2696_, v_es_2699_);
                    v___x_2703_ = lean_unsigned_to_nat(1);
                    v___x_2704_ = lean_nat_add(v_i_2694_, v___x_2703_);
                    lean_dec(v_i_2694_);
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
    mut v_data_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    v___x_2707_ = lean_array_get_size(v_data_2706_);
    v___x_2708_ = lean_unsigned_to_nat(2);
    v_nbuckets_2709_ = lean_nat_mul(v___x_2707_, v___x_2708_);
    v___x_2710_ = lean_unsigned_to_nat(0);
    v___x_2711_ = lean_box(0);
    v___x_2712_ = lean_mk_array(v_nbuckets_2709_, v___x_2711_);
    v___x_2713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_2710_, v_data_2706_, v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(
    mut v_a_2714_: *mut LeanObject,
    mut v_x_2715_: *mut LeanObject,
) -> u8 {
    let mut v___x_2716_: u8 = 0;
    let mut v_key_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2715_) == 0 {
                    v___x_2716_ = 0;
                    return v___x_2716_;
                } else {
                    v_key_2717_ = lean_ctor_get(v_x_2715_, 0);
                    v_tail_2718_ = lean_ctor_get(v_x_2715_, 2);
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
    mut v_a_2721_: *mut LeanObject,
    mut v_x_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2723_: u8 = 0;
    let mut v_r_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_2721_, v_x_2722_);
    lean_dec(v_x_2722_);
    lean_dec_ref(v_a_2721_);
    v_r_2724_ = lean_box((v_res_2723_) as usize);
    return v_r_2724_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(
    mut v_a_2725_: *mut LeanObject,
    mut v_b_2726_: *mut LeanObject,
    mut v_x_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2727_) == 0 {
                    lean_dec(v_b_2726_);
                    lean_dec_ref(v_a_2725_);
                    return v_x_2727_;
                } else {
                    v_key_2728_ = lean_ctor_get(v_x_2727_, 0);
                    v_value_2729_ = lean_ctor_get(v_x_2727_, 1);
                    v_tail_2730_ = lean_ctor_get(v_x_2727_, 2);
                    v_isSharedCheck_2742_ = (!lean_is_exclusive(v_x_2727_)) as u8;
                    if v_isSharedCheck_2742_ == 0 {
                        v___x_2732_ = v_x_2727_;
                        v_isShared_2733_ = v_isSharedCheck_2742_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2730_);
                        lean_inc(v_value_2729_);
                        lean_inc(v_key_2728_);
                        lean_dec(v_x_2727_);
                        v___x_2732_ = lean_box(0);
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
                        lean_ctor_set(v___x_2732_, 2, v___x_2735_);
                        v___x_2737_ = v___x_2732_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_key_2728_);
                        lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_value_2729_);
                        lean_ctor_set(v_reuseFailAlloc_2738_, 2, v___x_2735_);
                        v___x_2737_ = v_reuseFailAlloc_2738_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2729_);
                    lean_dec(v_key_2728_);
                    if v_isShared_2733_ == 0 {
                        lean_ctor_set(v___x_2732_, 1, v_b_2726_);
                        lean_ctor_set(v___x_2732_, 0, v_a_2725_);
                        v___x_2740_ = v___x_2732_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2725_);
                        lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_b_2726_);
                        lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_tail_2730_);
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
    mut v_m_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_b_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v_val_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2746_ = lean_ctor_get(v_m_2743_, 0);
                v_buckets_2747_ = lean_ctor_get(v_m_2743_, 1);
                v_isSharedCheck_2790_ = (!lean_is_exclusive(v_m_2743_)) as u8;
                if v_isSharedCheck_2790_ == 0 {
                    v___x_2749_ = v_m_2743_;
                    v_isShared_2750_ = v_isSharedCheck_2790_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2747_);
                    lean_inc(v_size_2746_);
                    lean_dec(v_m_2743_);
                    v___x_2749_ = lean_box(0);
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
                    v___x_2766_ = lean_unsigned_to_nat(1);
                    v_size_x27_2767_ = lean_nat_add(v_size_2746_, v___x_2766_);
                    lean_dec(v_size_2746_);
                    lean_inc(v_bkt_2764_);
                    v___x_2768_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2768_, 0, v_a_2744_);
                    lean_ctor_set(v___x_2768_, 1, v_b_2745_);
                    lean_ctor_set(v___x_2768_, 2, v_bkt_2764_);
                    v_buckets_x27_2769_ =
                        lean_array_uset(v_buckets_2747_, v___x_2763_, v___x_2768_);
                    v___x_2770_ = lean_unsigned_to_nat(4);
                    v___x_2771_ = lean_nat_mul(v_size_x27_2767_, v___x_2770_);
                    v___x_2772_ = lean_unsigned_to_nat(3);
                    v___x_2773_ = lean_nat_div(v___x_2771_, v___x_2772_);
                    lean_dec(v___x_2771_);
                    v___x_2774_ = lean_array_get_size(v_buckets_x27_2769_);
                    v___x_2775_ = lean_nat_dec_le(v___x_2773_, v___x_2774_);
                    lean_dec(v___x_2773_);
                    if v___x_2775_ == 0 {
                        v_val_2776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_2769_);
                        if v_isShared_2750_ == 0 {
                            lean_ctor_set(v___x_2749_, 1, v_val_2776_);
                            lean_ctor_set(v___x_2749_, 0, v_size_x27_2767_);
                            v___x_2778_ = v___x_2749_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_size_x27_2767_);
                            lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_val_2776_);
                            v___x_2778_ = v_reuseFailAlloc_2779_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2750_ == 0 {
                            lean_ctor_set(v___x_2749_, 1, v_buckets_x27_2769_);
                            lean_ctor_set(v___x_2749_, 0, v_size_x27_2767_);
                            v___x_2781_ = v___x_2749_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_size_x27_2767_);
                            lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_buckets_x27_2769_);
                            v___x_2781_ = v_reuseFailAlloc_2782_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2764_);
                    v___x_2783_ = lean_box(0);
                    v_buckets_x27_2784_ =
                        lean_array_uset(v_buckets_2747_, v___x_2763_, v___x_2783_);
                    v___x_2785_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_2744_, v_b_2745_, v_bkt_2764_);
                    v___x_2786_ = lean_array_uset(v_buckets_x27_2784_, v___x_2763_, v___x_2785_);
                    if v_isShared_2750_ == 0 {
                        lean_ctor_set(v___x_2749_, 1, v___x_2786_);
                        v___x_2788_ = v___x_2749_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_size_2746_);
                        lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
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
-> *mut LeanObject {
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1;
    v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
    return v___x_2795_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3;
    v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
    return v___x_2798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(
    mut v_val_2811_: *mut LeanObject,
    mut v___x_2812_: u8,
    mut v_ci_2813_: *mut LeanObject,
    mut v_info_2814_: *mut LeanObject,
    mut v_x_2815_: *mut LeanObject,
    mut v___y_2816_: *mut LeanObject,
    mut v___y_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v_maskAcc_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v_snd_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_unused_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_unused_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_2814_) == 10 {
                    v_i_2819_ = lean_ctor_get(v_info_2814_, 0);
                    lean_inc_ref(v_i_2819_);
                    v_stx_2820_ = lean_ctor_get(v_i_2819_, 0);
                    v_value_2821_ = lean_ctor_get(v_i_2819_, 1);
                    v_isSharedCheck_2916_ = (!lean_is_exclusive(v_i_2819_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2823_ = v_i_2819_;
                        v_isShared_2824_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_value_2821_);
                        lean_inc(v_stx_2820_);
                        lean_dec(v_i_2819_);
                        v___x_2823_ = lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_info_2814_);
                    v___x_2917_ = lean_box(0);
                    v___x_2918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2918_, 0, v___x_2917_);
                    return v___x_2918_;
                }
            }
            1 => {
                v___x_2825_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
                v___x_2826_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_value_2821_,
                    v___x_2825_,
                );
                lean_dec(v_value_2821_);
                if lean_obj_tag(v___x_2826_) == 1 {
                    v_val_2827_ = lean_ctor_get(v___x_2826_, 0);
                    v_isSharedCheck_2906_ = (!lean_is_exclusive(v___x_2826_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2829_ = v___x_2826_;
                        v_isShared_2830_ = v_isSharedCheck_2906_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2827_);
                        lean_dec(v___x_2826_);
                        v___x_2829_ = lean_box(0);
                        v_isShared_2830_ = v_isSharedCheck_2906_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2826_);
                    lean_del_object(v___x_2823_);
                    lean_dec(v_stx_2820_);
                    v_isSharedCheck_2914_ = (!lean_is_exclusive(v_info_2814_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v_unused_2915_ = lean_ctor_get(v_info_2814_, 0);
                        lean_dec(v_unused_2915_);
                        v___x_2908_ = v_info_2814_;
                        v_isShared_2909_ = v_isSharedCheck_2914_;
                        state = 17;
                        continue;
                    } else {
                        lean_dec(v_info_2814_);
                        v___x_2908_ = lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2914_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2831_ = l_Lean_Elab_Info_range_x3f(v_info_2814_);
                if lean_obj_tag(v___x_2831_) == 1 {
                    v_val_2832_ = lean_ctor_get(v___x_2831_, 0);
                    v_isSharedCheck_2901_ = (!lean_is_exclusive(v___x_2831_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2834_ = v___x_2831_;
                        v_isShared_2835_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2832_);
                        lean_dec(v___x_2831_);
                        v___x_2834_ = lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2831_);
                    lean_dec(v_val_2827_);
                    lean_del_object(v___x_2823_);
                    lean_dec(v_stx_2820_);
                    lean_dec_ref_known(v_info_2814_, 1);
                    v___x_2902_ = lean_box(0);
                    if v_isShared_2830_ == 0 {
                        lean_ctor_set_tag(v___x_2829_, 0);
                        lean_ctor_set(v___x_2829_, 0, v___x_2902_);
                        v___x_2904_ = v___x_2829_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
                        v___x_2904_ = v_reuseFailAlloc_2905_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6;
                lean_inc(v_stx_2820_);
                v___x_2889_ = l_Lean_Syntax_isOfKind(v_stx_2820_, v___x_2888_);
                if v___x_2889_ == 0 {
                    v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8;
                    lean_inc(v_stx_2820_);
                    v___x_2891_ = l_Lean_Syntax_isOfKind(v_stx_2820_, v___x_2890_);
                    if v___x_2891_ == 0 {
                        lean_del_object(v___x_2834_);
                        lean_dec(v_val_2832_);
                        lean_del_object(v___x_2829_);
                        lean_dec(v_val_2827_);
                        lean_del_object(v___x_2823_);
                        lean_dec(v_stx_2820_);
                        v_isSharedCheck_2899_ = (!lean_is_exclusive(v_info_2814_)) as u8;
                        if v_isSharedCheck_2899_ == 0 {
                            v_unused_2900_ = lean_ctor_get(v_info_2814_, 0);
                            lean_dec(v_unused_2900_);
                            v___x_2893_ = v_info_2814_;
                            v_isShared_2894_ = v_isSharedCheck_2899_;
                            state = 14;
                            continue;
                        } else {
                            lean_dec(v_info_2814_);
                            v___x_2893_ = lean_box(0);
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
                    lean_ctor_set(v___x_2823_, 1, v_maskAcc_2837_);
                    v___x_2840_ = v___x_2823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_stx_2820_);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_maskAcc_2837_);
                    v___x_2840_ = v_reuseFailAlloc_2846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_2838_, v_val_2832_, v___x_2840_);
                v___x_2842_ = lean_st_ref_set(v_val_2811_, v___x_2841_);
                if v_isShared_2835_ == 0 {
                    lean_ctor_set_tag(v___x_2834_, 0);
                    lean_ctor_set(v___x_2834_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2844_;
            }
            7 => {
                v___x_2849_ = lean_unsigned_to_nat(0);
                v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0;
                v___x_2851_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(
                    v___x_2812_,
                    v_val_2827_,
                    v___y_2848_,
                    v___x_2849_,
                    v___x_2850_,
                );
                lean_dec_ref(v___y_2848_);
                lean_dec(v_val_2827_);
                v_maskAcc_2837_ = v___x_2851_;
                state = 4;
                continue;
            }
            8 => {
                v___x_2853_ = lean_st_ref_get(v_val_2811_);
                v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_2853_, v_val_2832_);
                lean_dec(v___x_2853_);
                if lean_obj_tag(v___x_2854_) == 1 {
                    v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
                    v_isSharedCheck_2887_ = (!lean_is_exclusive(v___x_2854_)) as u8;
                    if v_isSharedCheck_2887_ == 0 {
                        v___x_2857_ = v___x_2854_;
                        v_isShared_2858_ = v_isSharedCheck_2887_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_2855_);
                        lean_dec(v___x_2854_);
                        v___x_2857_ = lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2887_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2854_);
                    lean_del_object(v___x_2829_);
                    lean_dec_ref_known(v_info_2814_, 1);
                    v_maskAcc_2837_ = v_val_2827_;
                    state = 4;
                    continue;
                }
            }
            9 => {
                v_snd_2859_ = lean_ctor_get(v_val_2855_, 1);
                v_isSharedCheck_2885_ = (!lean_is_exclusive(v_val_2855_)) as u8;
                if v_isSharedCheck_2885_ == 0 {
                    v_unused_2886_ = lean_ctor_get(v_val_2855_, 0);
                    lean_dec(v_unused_2886_);
                    v___x_2861_ = v_val_2855_;
                    v_isShared_2862_ = v_isSharedCheck_2885_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_snd_2859_);
                    lean_dec(v_val_2855_);
                    v___x_2861_ = lean_box(0);
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
                    lean_dec_ref_known(v_info_2814_, 1);
                    v___x_2867_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
                    v___x_2868_ = l_Nat_reprFast(v___x_2864_);
                    if v_isShared_2858_ == 0 {
                        lean_ctor_set_tag(v___x_2857_, 3);
                        lean_ctor_set(v___x_2857_, 0, v___x_2868_);
                        v___x_2870_ = v___x_2857_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2884_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2868_);
                        v___x_2870_ = v_reuseFailAlloc_2884_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2861_);
                    lean_del_object(v___x_2857_);
                    lean_del_object(v___x_2829_);
                    lean_dec_ref_known(v_info_2814_, 1);
                    v___y_2848_ = v_snd_2859_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                v___x_2871_ = l_Lean_MessageData_ofFormat(v___x_2870_);
                if v_isShared_2862_ == 0 {
                    lean_ctor_set_tag(v___x_2861_, 7);
                    lean_ctor_set(v___x_2861_, 1, v___x_2871_);
                    lean_ctor_set(v___x_2861_, 0, v___x_2867_);
                    v___x_2873_ = v___x_2861_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2867_);
                    lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2871_);
                    v___x_2873_ = v_reuseFailAlloc_2883_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2874_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
                v___x_2875_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2875_, 0, v___x_2873_);
                lean_ctor_set(v___x_2875_, 1, v___x_2874_);
                v___x_2876_ = l_Nat_reprFast(v___x_2863_);
                if v_isShared_2830_ == 0 {
                    lean_ctor_set_tag(v___x_2829_, 3);
                    lean_ctor_set(v___x_2829_, 0, v___x_2876_);
                    v___x_2878_ = v___x_2829_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2882_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
                    v___x_2878_ = v_reuseFailAlloc_2882_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2879_ = l_Lean_MessageData_ofFormat(v___x_2878_);
                v___x_2880_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2880_, 0, v___x_2875_);
                lean_ctor_set(v___x_2880_, 1, v___x_2879_);
                v___x_2881_ =
                    l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
                        v___x_2866_,
                        v___x_2880_,
                        v___y_2816_,
                        v___y_2817_,
                    );
                lean_dec(v___x_2866_);
                if lean_obj_tag(v___x_2881_) == 0 {
                    lean_dec_ref_known(v___x_2881_, 1);
                    v___y_2848_ = v_snd_2859_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v_snd_2859_);
                    lean_del_object(v___x_2834_);
                    lean_dec(v_val_2832_);
                    lean_dec(v_val_2827_);
                    lean_del_object(v___x_2823_);
                    lean_dec(v_stx_2820_);
                    return v___x_2881_;
                }
            }
            14 => {
                v___x_2895_ = lean_box(0);
                if v_isShared_2894_ == 0 {
                    lean_ctor_set_tag(v___x_2893_, 0);
                    lean_ctor_set(v___x_2893_, 0, v___x_2895_);
                    v___x_2897_ = v___x_2893_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
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
                v___x_2910_ = lean_box(0);
                if v_isShared_2909_ == 0 {
                    lean_ctor_set_tag(v___x_2908_, 0);
                    lean_ctor_set(v___x_2908_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2908_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
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
    mut v_val_2919_: *mut LeanObject,
    mut v___x_2920_: *mut LeanObject,
    mut v_ci_2921_: *mut LeanObject,
    mut v_info_2922_: *mut LeanObject,
    mut v_x_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14717__boxed_2927_: u8 = 0;
    let mut v_res_2928_: *mut LeanObject = core::ptr::null_mut();
    v___x_14717__boxed_2927_ = (lean_unbox(v___x_2920_) as u8);
    v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v_val_2919_, v___x_14717__boxed_2927_, v_ci_2921_, v_info_2922_, v_x_2923_, v___y_2924_, v___y_2925_);
    lean_dec(v___y_2925_);
    lean_dec_ref(v___y_2924_);
    lean_dec_ref(v_x_2923_);
    lean_dec_ref(v_ci_2921_);
    lean_dec(v_val_2919_);
    return v_res_2928_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(
    mut v_postNode_2929_: *mut LeanObject,
    mut v_ci_2930_: *mut LeanObject,
    mut v_i_2931_: *mut LeanObject,
    mut v_cs_2932_: *mut LeanObject,
    mut v_x_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2935_);
    lean_inc_ref(v___y_2934_);
    v___x_2937_ = lean_apply_6(
        v_postNode_2929_,
        v_ci_2930_,
        v_i_2931_,
        v_cs_2932_,
        v___y_2934_,
        v___y_2935_,
        lean_box(0),
    );
    return v___x_2937_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(
    mut v_postNode_2938_: *mut LeanObject,
    mut v_ci_2939_: *mut LeanObject,
    mut v_i_2940_: *mut LeanObject,
    mut v_cs_2941_: *mut LeanObject,
    mut v_x_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2944_);
    lean_dec_ref(v___y_2943_);
    lean_dec(v_x_2942_);
    return v_res_2946_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_instMonadEIO(lean_box(0));
    return v___x_2947_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(
    mut v_msg_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v_toFunctor_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___f_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_13235__overap_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
                v___x_2955_ = l_StateRefT_x27_instMonad___redArg(v___x_2954_);
                v_toApplicative_2956_ = lean_ctor_get(v___x_2955_, 0);
                v_isSharedCheck_2987_ = (!lean_is_exclusive(v___x_2955_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v_unused_2988_ = lean_ctor_get(v___x_2955_, 1);
                    lean_dec(v_unused_2988_);
                    v___x_2958_ = v___x_2955_;
                    v_isShared_2959_ = v_isSharedCheck_2987_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2956_);
                    lean_dec(v___x_2955_);
                    v___x_2958_ = lean_box(0);
                    v_isShared_2959_ = v_isSharedCheck_2987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2960_ = lean_ctor_get(v_toApplicative_2956_, 0);
                v_toSeq_2961_ = lean_ctor_get(v_toApplicative_2956_, 2);
                v_toSeqLeft_2962_ = lean_ctor_get(v_toApplicative_2956_, 3);
                v_toSeqRight_2963_ = lean_ctor_get(v_toApplicative_2956_, 4);
                v_isSharedCheck_2985_ = (!lean_is_exclusive(v_toApplicative_2956_)) as u8;
                if v_isSharedCheck_2985_ == 0 {
                    v_unused_2986_ = lean_ctor_get(v_toApplicative_2956_, 1);
                    lean_dec(v_unused_2986_);
                    v___x_2965_ = v_toApplicative_2956_;
                    v_isShared_2966_ = v_isSharedCheck_2985_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2963_);
                    lean_inc(v_toSeqLeft_2962_);
                    lean_inc(v_toSeq_2961_);
                    lean_inc(v_toFunctor_2960_);
                    lean_dec(v_toApplicative_2956_);
                    v___x_2965_ = lean_box(0);
                    v_isShared_2966_ = v_isSharedCheck_2985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2967_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1;
                v___f_2968_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2;
                lean_inc_ref(v_toFunctor_2960_);
                v___f_2969_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2969_, 0, v_toFunctor_2960_);
                v___f_2970_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2970_, 0, v_toFunctor_2960_);
                v___x_2971_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2971_, 0, v___f_2969_);
                lean_ctor_set(v___x_2971_, 1, v___f_2970_);
                v___f_2972_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2972_, 0, v_toSeqRight_2963_);
                v___f_2973_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2973_, 0, v_toSeqLeft_2962_);
                v___f_2974_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2974_, 0, v_toSeq_2961_);
                if v_isShared_2966_ == 0 {
                    lean_ctor_set(v___x_2965_, 4, v___f_2972_);
                    lean_ctor_set(v___x_2965_, 3, v___f_2973_);
                    lean_ctor_set(v___x_2965_, 2, v___f_2974_);
                    lean_ctor_set(v___x_2965_, 1, v___f_2967_);
                    lean_ctor_set(v___x_2965_, 0, v___x_2971_);
                    v___x_2976_ = v___x_2965_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2971_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___f_2967_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 2, v___f_2974_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 3, v___f_2973_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 4, v___f_2972_);
                    v___x_2976_ = v_reuseFailAlloc_2984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2959_ == 0 {
                    lean_ctor_set(v___x_2958_, 1, v___f_2968_);
                    lean_ctor_set(v___x_2958_, 0, v___x_2976_);
                    v___x_2978_ = v___x_2958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2976_);
                    lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___f_2968_);
                    v___x_2978_ = v_reuseFailAlloc_2983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2979_ = lean_box(0);
                v___x_2980_ = l_instInhabitedOfMonad___redArg(v___x_2978_, v___x_2979_);
                v___x_13235__overap_2981_ = lean_panic_fn_borrowed(v___x_2980_, v_msg_2950_);
                lean_dec(v___x_2980_);
                lean_inc(v___y_2952_);
                lean_inc_ref(v___y_2951_);
                v___x_2982_ = lean_apply_3(
                    v___x_13235__overap_2981_,
                    v___y_2951_,
                    v___y_2952_,
                    lean_box(0),
                );
                return v___x_2982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(
    mut v_msg_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_2989_, v___y_2990_, v___y_2991_);
    lean_dec(v___y_2991_);
    lean_dec_ref(v___y_2990_);
    return v_res_2993_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2997_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2;
    v___x_2998_ = lean_unsigned_to_nat(21);
    v___x_2999_ = lean_unsigned_to_nat(65);
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
    mut v_preNode_3003_: *mut LeanObject,
    mut v_postNode_3004_: *mut LeanObject,
    mut v_x_3005_: *mut LeanObject,
    mut v_x_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_unused_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_a_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_a_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut v_unused_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3006_) {
                0 => {
                    v_i_3010_ = lean_ctor_get(v_x_3006_, 0);
                    lean_inc_ref(v_i_3010_);
                    v_t_3011_ = lean_ctor_get(v_x_3006_, 1);
                    lean_inc_ref(v_t_3011_);
                    lean_dec_ref_known(v_x_3006_, 2);
                    v___x_3012_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3010_, v_x_3005_);
                    v_x_3005_ = v___x_3012_;
                    v_x_3006_ = v_t_3011_;
                    state = 0;
                    continue;
                }
                1 => {
                    if lean_obj_tag(v_x_3005_) == 0 {
                        lean_dec_ref_known(v_x_3006_, 2);
                        lean_dec_ref(v_postNode_3004_);
                        lean_dec_ref(v_preNode_3003_);
                        v___x_3014_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
                        v___x_3015_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_3014_, v___y_3007_, v___y_3008_);
                        return v___x_3015_;
                    } else {
                        v_i_3016_ = lean_ctor_get(v_x_3006_, 0);
                        lean_inc_ref_n(v_i_3016_, 2);
                        v_children_3017_ = lean_ctor_get(v_x_3006_, 1);
                        lean_inc_ref_n(v_children_3017_, 2);
                        lean_dec_ref_known(v_x_3006_, 2);
                        v_val_3018_ = lean_ctor_get(v_x_3005_, 0);
                        lean_inc_n(v_val_3018_, 2);
                        lean_inc_ref(v_preNode_3003_);
                        lean_inc(v___y_3008_);
                        lean_inc_ref(v___y_3007_);
                        v___x_3019_ = lean_apply_6(
                            v_preNode_3003_,
                            v_val_3018_,
                            v_i_3016_,
                            v_children_3017_,
                            v___y_3007_,
                            v___y_3008_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_3019_) == 0 {
                            v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
                            lean_inc(v_a_3020_);
                            lean_dec_ref_known(v___x_3019_, 1);
                            v___x_3021_ = (lean_unbox(v_a_3020_) as u8);
                            lean_dec(v_a_3020_);
                            if v___x_3021_ == 0 {
                                lean_dec_ref(v_preNode_3003_);
                                v_isSharedCheck_3046_ = (!lean_is_exclusive(v_x_3005_)) as u8;
                                if v_isSharedCheck_3046_ == 0 {
                                    v_unused_3047_ = lean_ctor_get(v_x_3005_, 0);
                                    lean_dec(v_unused_3047_);
                                    v___x_3023_ = v_x_3005_;
                                    v_isShared_3024_ = v_isSharedCheck_3046_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_x_3005_);
                                    v___x_3023_ = lean_box(0);
                                    v_isShared_3024_ = v_isSharedCheck_3046_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_3048_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_3005_, v_i_3016_);
                                v___x_3049_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_3017_);
                                v___x_3050_ = lean_box(0);
                                lean_inc_ref(v_postNode_3004_);
                                v___x_3051_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3003_, v_postNode_3004_, v___x_3048_, v___x_3049_, v___x_3050_, v___y_3007_, v___y_3008_);
                                if lean_obj_tag(v___x_3051_) == 0 {
                                    v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
                                    lean_inc(v_a_3052_);
                                    lean_dec_ref_known(v___x_3051_, 1);
                                    lean_inc(v___y_3008_);
                                    lean_inc_ref(v___y_3007_);
                                    v___x_3053_ = lean_apply_7(
                                        v_postNode_3004_,
                                        v_val_3018_,
                                        v_i_3016_,
                                        v_children_3017_,
                                        v_a_3052_,
                                        v___y_3007_,
                                        v___y_3008_,
                                        lean_box(0),
                                    );
                                    if lean_obj_tag(v___x_3053_) == 0 {
                                        v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
                                        v_isSharedCheck_3062_ =
                                            (!lean_is_exclusive(v___x_3053_)) as u8;
                                        if v_isSharedCheck_3062_ == 0 {
                                            v___x_3056_ = v___x_3053_;
                                            v_isShared_3057_ = v_isSharedCheck_3062_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3054_);
                                            lean_dec(v___x_3053_);
                                            v___x_3056_ = lean_box(0);
                                            v_isShared_3057_ = v_isSharedCheck_3062_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_3063_ = lean_ctor_get(v___x_3053_, 0);
                                        v_isSharedCheck_3070_ =
                                            (!lean_is_exclusive(v___x_3053_)) as u8;
                                        if v_isSharedCheck_3070_ == 0 {
                                            v___x_3065_ = v___x_3053_;
                                            v_isShared_3066_ = v_isSharedCheck_3070_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3063_);
                                            lean_dec(v___x_3053_);
                                            v___x_3065_ = lean_box(0);
                                            v_isShared_3066_ = v_isSharedCheck_3070_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_3018_);
                                    lean_dec_ref(v_children_3017_);
                                    lean_dec_ref(v_i_3016_);
                                    lean_dec_ref(v_postNode_3004_);
                                    v_a_3071_ = lean_ctor_get(v___x_3051_, 0);
                                    v_isSharedCheck_3078_ = (!lean_is_exclusive(v___x_3051_)) as u8;
                                    if v_isSharedCheck_3078_ == 0 {
                                        v___x_3073_ = v___x_3051_;
                                        v_isShared_3074_ = v_isSharedCheck_3078_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3071_);
                                        lean_dec(v___x_3051_);
                                        v___x_3073_ = lean_box(0);
                                        v_isShared_3074_ = v_isSharedCheck_3078_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_val_3018_);
                            lean_dec_ref(v_children_3017_);
                            lean_dec_ref_known(v_x_3005_, 1);
                            lean_dec_ref(v_i_3016_);
                            lean_dec_ref(v_postNode_3004_);
                            lean_dec_ref(v_preNode_3003_);
                            v_a_3079_ = lean_ctor_get(v___x_3019_, 0);
                            v_isSharedCheck_3086_ = (!lean_is_exclusive(v___x_3019_)) as u8;
                            if v_isSharedCheck_3086_ == 0 {
                                v___x_3081_ = v___x_3019_;
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_3079_);
                                lean_dec(v___x_3019_);
                                v___x_3081_ = lean_box(0);
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    lean_dec(v_x_3005_);
                    lean_dec_ref(v_postNode_3004_);
                    lean_dec_ref(v_preNode_3003_);
                    v_isSharedCheck_3094_ = (!lean_is_exclusive(v_x_3006_)) as u8;
                    if v_isSharedCheck_3094_ == 0 {
                        v_unused_3095_ = lean_ctor_get(v_x_3006_, 0);
                        lean_dec(v_unused_3095_);
                        v___x_3088_ = v_x_3006_;
                        v_isShared_3089_ = v_isSharedCheck_3094_;
                        state = 15;
                        continue;
                    } else {
                        lean_dec(v_x_3006_);
                        v___x_3088_ = lean_box(0);
                        v_isShared_3089_ = v_isSharedCheck_3094_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3025_ = lean_box(0);
                lean_inc(v___y_3008_);
                lean_inc_ref(v___y_3007_);
                v___x_3026_ = lean_apply_7(
                    v_postNode_3004_,
                    v_val_3018_,
                    v_i_3016_,
                    v_children_3017_,
                    v___x_3025_,
                    v___y_3007_,
                    v___y_3008_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3026_) == 0 {
                    v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
                    v_isSharedCheck_3037_ = (!lean_is_exclusive(v___x_3026_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3029_ = v___x_3026_;
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3027_);
                        lean_dec(v___x_3026_);
                        v___x_3029_ = lean_box(0);
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3023_);
                    v_a_3038_ = lean_ctor_get(v___x_3026_, 0);
                    v_isSharedCheck_3045_ = (!lean_is_exclusive(v___x_3026_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_3040_ = v___x_3026_;
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3038_);
                        lean_dec(v___x_3026_);
                        v___x_3040_ = lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3024_ == 0 {
                    lean_ctor_set(v___x_3023_, 0, v_a_3027_);
                    v___x_3032_ = v___x_3023_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3030_ == 0 {
                    lean_ctor_set(v___x_3029_, 0, v___x_3032_);
                    v___x_3034_ = v___x_3029_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
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
                    v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
                    v___x_3043_ = v_reuseFailAlloc_3044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3043_;
            }
            7 => {
                v___x_3058_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3058_, 0, v_a_3054_);
                if v_isShared_3057_ == 0 {
                    lean_ctor_set(v___x_3056_, 0, v___x_3058_);
                    v___x_3060_ = v___x_3056_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
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
                    v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
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
                    v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
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
                    v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3084_;
            }
            15 => {
                v___x_3090_ = lean_box(0);
                if v_isShared_3089_ == 0 {
                    lean_ctor_set_tag(v___x_3088_, 0);
                    lean_ctor_set(v___x_3088_, 0, v___x_3090_);
                    v___x_3092_ = v___x_3088_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
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
    mut v_preNode_3096_: *mut LeanObject,
    mut v_postNode_3097_: *mut LeanObject,
    mut v___x_3098_: *mut LeanObject,
    mut v_x_3099_: *mut LeanObject,
    mut v_x_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3099_) == 0 {
                    lean_dec(v___x_3098_);
                    lean_dec_ref(v_postNode_3097_);
                    lean_dec_ref(v_preNode_3096_);
                    v___x_3104_ = l_List_reverse___redArg(v_x_3100_);
                    v___x_3105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3105_, 0, v___x_3104_);
                    return v___x_3105_;
                } else {
                    v_head_3106_ = lean_ctor_get(v_x_3099_, 0);
                    v_tail_3107_ = lean_ctor_get(v_x_3099_, 1);
                    v_isSharedCheck_3125_ = (!lean_is_exclusive(v_x_3099_)) as u8;
                    if v_isSharedCheck_3125_ == 0 {
                        v___x_3109_ = v_x_3099_;
                        v_isShared_3110_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3107_);
                        lean_inc(v_head_3106_);
                        lean_dec(v_x_3099_);
                        v___x_3109_ = lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_3098_);
                lean_inc_ref(v_postNode_3097_);
                lean_inc_ref(v_preNode_3096_);
                v___x_3111_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3096_, v_postNode_3097_, v___x_3098_, v_head_3106_, v___y_3101_, v___y_3102_);
                if lean_obj_tag(v___x_3111_) == 0 {
                    v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
                    lean_inc(v_a_3112_);
                    lean_dec_ref_known(v___x_3111_, 1);
                    if v_isShared_3110_ == 0 {
                        lean_ctor_set(v___x_3109_, 1, v_x_3100_);
                        lean_ctor_set(v___x_3109_, 0, v_a_3112_);
                        v___x_3114_ = v___x_3109_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3112_);
                        lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_x_3100_);
                        v___x_3114_ = v_reuseFailAlloc_3116_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3109_);
                    lean_dec(v_tail_3107_);
                    lean_dec(v_x_3100_);
                    lean_dec(v___x_3098_);
                    lean_dec_ref(v_postNode_3097_);
                    lean_dec_ref(v_preNode_3096_);
                    v_a_3117_ = lean_ctor_get(v___x_3111_, 0);
                    v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3111_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3119_ = v___x_3111_;
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3117_);
                        lean_dec(v___x_3111_);
                        v___x_3119_ = lean_box(0);
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
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
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
    mut v_preNode_3126_: *mut LeanObject,
    mut v_postNode_3127_: *mut LeanObject,
    mut v___x_3128_: *mut LeanObject,
    mut v_x_3129_: *mut LeanObject,
    mut v_x_3130_: *mut LeanObject,
    mut v___y_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3134_: *mut LeanObject = core::ptr::null_mut();
    v_res_3134_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3126_, v_postNode_3127_, v___x_3128_, v_x_3129_, v_x_3130_, v___y_3131_, v___y_3132_);
    lean_dec(v___y_3132_);
    lean_dec_ref(v___y_3131_);
    return v_res_3134_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(
    mut v_preNode_3135_: *mut LeanObject,
    mut v_postNode_3136_: *mut LeanObject,
    mut v_x_3137_: *mut LeanObject,
    mut v_x_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3142_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3135_, v_postNode_3136_, v_x_3137_, v_x_3138_, v___y_3139_, v___y_3140_);
    lean_dec(v___y_3140_);
    lean_dec_ref(v___y_3139_);
    return v_res_3142_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
    mut v_preNode_3143_: *mut LeanObject,
    mut v_postNode_3144_: *mut LeanObject,
    mut v_ctx_x3f_3145_: *mut LeanObject,
    mut v_t_3146_: *mut LeanObject,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_unused_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3150_ = lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3150_, 0, v_postNode_3144_);
                v___x_3151_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3143_, v___f_3150_, v_ctx_x3f_3145_, v_t_3146_, v___y_3147_, v___y_3148_);
                if lean_obj_tag(v___x_3151_) == 0 {
                    v_isSharedCheck_3159_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3159_ == 0 {
                        v_unused_3160_ = lean_ctor_get(v___x_3151_, 0);
                        lean_dec(v_unused_3160_);
                        v___x_3153_ = v___x_3151_;
                        v_isShared_3154_ = v_isSharedCheck_3159_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3151_);
                        v___x_3153_ = lean_box(0);
                        v_isShared_3154_ = v_isSharedCheck_3159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3161_ = lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3168_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3163_ = v___x_3151_;
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3161_);
                        lean_dec(v___x_3151_);
                        v___x_3163_ = lean_box(0);
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3155_ = lean_box(0);
                if v_isShared_3154_ == 0 {
                    lean_ctor_set(v___x_3153_, 0, v___x_3155_);
                    v___x_3157_ = v___x_3153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
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
                    v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
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
    mut v_preNode_3169_: *mut LeanObject,
    mut v_postNode_3170_: *mut LeanObject,
    mut v_ctx_x3f_3171_: *mut LeanObject,
    mut v_t_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3176_: *mut LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
        v_preNode_3169_,
        v_postNode_3170_,
        v_ctx_x3f_3171_,
        v_t_3172_,
        v___y_3173_,
        v___y_3174_,
    );
    lean_dec(v___y_3174_);
    lean_dec_ref(v___y_3173_);
    return v_res_3176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(
    mut v___x_3177_: u8,
    mut v_x_3178_: *mut LeanObject,
    mut v_x_3179_: *mut LeanObject,
    mut v_x_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    v___x_3184_ = lean_box((v___x_3177_) as usize);
    v___x_3185_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3185_, 0, v___x_3184_);
    return v___x_3185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(
    mut v___x_3186_: *mut LeanObject,
    mut v_x_3187_: *mut LeanObject,
    mut v_x_3188_: *mut LeanObject,
    mut v_x_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15366__boxed_3193_: u8 = 0;
    let mut v_res_3194_: *mut LeanObject = core::ptr::null_mut();
    v___x_15366__boxed_3193_ = (lean_unbox(v___x_3186_) as u8);
    v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_15366__boxed_3193_, v_x_3187_, v_x_3188_, v_x_3189_, v___y_3190_, v___y_3191_);
    lean_dec(v___y_3191_);
    lean_dec_ref(v___y_3190_);
    lean_dec_ref(v_x_3189_);
    lean_dec_ref(v_x_3188_);
    lean_dec_ref(v_x_3187_);
    return v_res_3194_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(
    mut v___x_3195_: u8,
    mut v_val_3196_: *mut LeanObject,
    mut v_as_3197_: *mut LeanObject,
    mut v_sz_3198_: usize,
    mut v_i_3199_: usize,
    mut v_b_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3204_ = lean_usize_dec_lt(v_i_3199_, v_sz_3198_);
                if v___x_3204_ == 0 {
                    lean_dec(v_val_3196_);
                    v___x_3205_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3205_, 0, v_b_3200_);
                    return v___x_3205_;
                } else {
                    v___x_3206_ = lean_box((v___x_3195_) as usize);
                    v___f_3207_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___f_3207_, 0, v___x_3206_);
                    v___x_3208_ = lean_box((v___x_3195_) as usize);
                    lean_inc(v_val_3196_);
                    v___f_3209_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed as *mut core::ffi::c_void, 8, 2);
                    lean_closure_set(v___f_3209_, 0, v_val_3196_);
                    lean_closure_set(v___f_3209_, 1, v___x_3208_);
                    v_a_3210_ = lean_array_uget_borrowed(v_as_3197_, v_i_3199_);
                    v___x_3211_ = lean_box(0);
                    lean_inc(v_a_3210_);
                    v___x_3212_ =
                        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(
                            v___f_3207_,
                            v___f_3209_,
                            v___x_3211_,
                            v_a_3210_,
                            v___y_3201_,
                            v___y_3202_,
                        );
                    if lean_obj_tag(v___x_3212_) == 0 {
                        lean_dec_ref_known(v___x_3212_, 1);
                        v___x_3213_ = lean_box(0);
                        v___x_3214_ = 1usize;
                        v___x_3215_ = lean_usize_add(v_i_3199_, v___x_3214_);
                        v_i_3199_ = v___x_3215_;
                        v_b_3200_ = v___x_3213_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_val_3196_);
                        return v___x_3212_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(
    mut v___x_3217_: *mut LeanObject,
    mut v_val_3218_: *mut LeanObject,
    mut v_as_3219_: *mut LeanObject,
    mut v_sz_3220_: *mut LeanObject,
    mut v_i_3221_: *mut LeanObject,
    mut v_b_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15391__boxed_3226_: u8 = 0;
    let mut v_sz_boxed_3227_: usize = 0;
    let mut v_i_boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut LeanObject = core::ptr::null_mut();
    v___x_15391__boxed_3226_ = (lean_unbox(v___x_3217_) as u8);
    v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3220_);
    lean_dec(v_sz_3220_);
    v_i_boxed_3228_ = lean_unbox_usize(v_i_3221_);
    lean_dec(v_i_3221_);
    v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_15391__boxed_3226_, v_val_3218_, v_as_3219_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3222_, v___y_3223_, v___y_3224_);
    lean_dec(v___y_3224_);
    lean_dec_ref(v___y_3223_);
    lean_dec_ref(v_as_3219_);
    return v_res_3229_;
}
pub unsafe fn _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    v___x_3230_ = lean_box(0);
    v___x_3231_ = lean_unsigned_to_nat(16);
    v___x_3232_ = lean_mk_array(v___x_3231_, v___x_3230_);
    return v___x_3232_;
}
pub unsafe fn _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3233_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_unusedSimpArgs___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once),
        _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0,
    );
    v___x_3234_ = lean_unsigned_to_nat(0);
    v___x_3235_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3235_, 0, v___x_3234_);
    lean_ctor_set(v___x_3235_, 1, v___x_3233_);
    return v___x_3235_;
}
pub unsafe fn l_Lean_Linter_unusedSimpArgs___lam__0(
    mut v_cmdStx_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: u8 = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3261_: usize = 0;
    let mut v___x_3262_: usize = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3267_: usize = 0;
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_unused_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___y_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v_size_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: u8 = 0;
    let mut v___x_3301_: u8 = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
                v_isSharedCheck_3310_ = (!lean_is_exclusive(v___x_3240_)) as u8;
                if v_isSharedCheck_3310_ == 0 {
                    v___x_3243_ = v___x_3240_;
                    v_isShared_3244_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3241_);
                    lean_dec(v___x_3240_);
                    v___x_3243_ = lean_box(0);
                    v_isShared_3244_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3245_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
                v___x_3246_ = l_Lean_Linter_getLinterValue(v___x_3245_, v_a_3241_);
                lean_dec(v_a_3241_);
                if v___x_3246_ == 0 {
                    v___x_3247_ = lean_box(0);
                    if v_isShared_3244_ == 0 {
                        lean_ctor_set(v___x_3243_, 0, v___x_3247_);
                        v___x_3249_ = v___x_3243_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
                        v___x_3249_ = v_reuseFailAlloc_3250_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3251_ = 0;
                    v___x_3252_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_3236_, v___x_3251_);
                    if lean_obj_tag(v___x_3252_) == 1 {
                        lean_dec_ref_known(v___x_3252_, 1);
                        lean_del_object(v___x_3243_);
                        v___x_3253_ = lean_st_ref_get(v___y_3238_);
                        v___x_3254_ = lean_unsigned_to_nat(0);
                        v___x_3255_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_unusedSimpArgs___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1,
                        );
                        v___x_3256_ = lean_st_mk_ref(v___x_3255_);
                        v_infoState_3257_ = lean_ctor_get(v___x_3253_, 8);
                        lean_inc_ref(v_infoState_3257_);
                        lean_dec(v___x_3253_);
                        v_trees_3258_ = lean_ctor_get(v_infoState_3257_, 2);
                        lean_inc_ref(v_trees_3258_);
                        lean_dec_ref(v_infoState_3257_);
                        v___x_3259_ = l_Lean_PersistentArray_toArray___redArg(v_trees_3258_);
                        lean_dec_ref(v_trees_3258_);
                        v___x_3260_ = lean_box(0);
                        v_sz_3261_ = lean_array_size(v___x_3259_);
                        v___x_3262_ = 0usize;
                        lean_inc(v___x_3256_);
                        v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_3246_, v___x_3256_, v___x_3259_, v_sz_3261_, v___x_3262_, v___x_3260_, v___y_3237_, v___y_3238_);
                        lean_dec_ref(v___x_3259_);
                        if lean_obj_tag(v___x_3263_) == 0 {
                            lean_dec_ref_known(v___x_3263_, 1);
                            v___x_3264_ = lean_st_ref_get(v___x_3256_);
                            lean_dec(v___x_3256_);
                            v_size_3296_ = lean_ctor_get(v___x_3264_, 0);
                            lean_inc(v_size_3296_);
                            v_buckets_3297_ = lean_ctor_get(v___x_3264_, 1);
                            lean_inc_ref(v_buckets_3297_);
                            lean_dec(v___x_3264_);
                            v___x_3298_ = lean_mk_empty_array_with_capacity(v_size_3296_);
                            lean_dec(v_size_3296_);
                            v___x_3299_ = lean_array_get_size(v_buckets_3297_);
                            v___x_3300_ = lean_nat_dec_lt(v___x_3254_, v___x_3299_);
                            if v___x_3300_ == 0 {
                                lean_dec_ref(v_buckets_3297_);
                                v___y_3290_ = v___x_3298_;
                                state = 8;
                                continue;
                            } else {
                                v___x_3301_ = lean_nat_dec_le(v___x_3299_, v___x_3299_);
                                if v___x_3301_ == 0 {
                                    if v___x_3300_ == 0 {
                                        lean_dec_ref(v_buckets_3297_);
                                        v___y_3290_ = v___x_3298_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_3302_ = lean_usize_of_nat(v___x_3299_);
                                        v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_3297_, v___x_3262_, v___x_3302_, v___x_3298_);
                                        lean_dec_ref(v_buckets_3297_);
                                        v___y_3290_ = v___x_3303_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v___x_3304_ = lean_usize_of_nat(v___x_3299_);
                                    v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_3297_, v___x_3262_, v___x_3304_, v___x_3298_);
                                    lean_dec_ref(v_buckets_3297_);
                                    v___y_3290_ = v___x_3305_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3256_);
                            return v___x_3263_;
                        }
                    } else {
                        lean_dec(v___x_3252_);
                        v___x_3306_ = lean_box(0);
                        if v_isShared_3244_ == 0 {
                            lean_ctor_set(v___x_3243_, 0, v___x_3306_);
                            v___x_3308_ = v___x_3243_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
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
                lean_dec_ref(v___y_3266_);
                if lean_obj_tag(v___x_3268_) == 0 {
                    v_isSharedCheck_3275_ = (!lean_is_exclusive(v___x_3268_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v_unused_3276_ = lean_ctor_get(v___x_3268_, 0);
                        lean_dec(v_unused_3276_);
                        v___x_3270_ = v___x_3268_;
                        v_isShared_3271_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_3268_);
                        v___x_3270_ = lean_box(0);
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
                    lean_ctor_set(v___x_3270_, 0, v___x_3260_);
                    v___x_3273_ = v___x_3270_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3260_);
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
                lean_dec(v___y_3281_);
                lean_dec(v___y_3280_);
                v___y_3266_ = v___x_3282_;
                state = 3;
                continue;
            }
            7 => {
                v___x_3288_ = lean_nat_dec_le(v___y_3287_, v___y_3285_);
                if v___x_3288_ == 0 {
                    lean_dec(v___y_3285_);
                    lean_inc(v___y_3287_);
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
                    v___x_3293_ = lean_unsigned_to_nat(1);
                    v___x_3294_ = lean_nat_sub(v___x_3291_, v___x_3293_);
                    v___x_3295_ = lean_nat_dec_le(v___x_3254_, v___x_3294_);
                    if v___x_3295_ == 0 {
                        lean_inc(v___x_3294_);
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
    mut v_cmdStx_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3315_: *mut LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_3311_, v___y_3312_, v___y_3313_);
    lean_dec(v___y_3313_);
    lean_dec_ref(v___y_3312_);
    lean_dec(v_cmdStx_3311_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(
    mut v_o_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_3327_, v___y_3329_);
    return v___x_3331_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(
    mut v_o_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_3332_, v___y_3333_, v___y_3334_);
    lean_dec(v___y_3334_);
    lean_dec_ref(v___y_3333_);
    return v_res_3336_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(
    mut v_00_u03b2_3337_: *mut LeanObject,
    mut v_m_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
    mut v_b_3340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_3338_, v_a_3339_, v_b_3340_);
    return v___x_3341_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(
    mut v_00_u03b2_3342_: *mut LeanObject,
    mut v_m_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_3343_, v_a_3344_);
    return v___x_3345_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(
    mut v_00_u03b2_3346_: *mut LeanObject,
    mut v_m_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3349_: *mut LeanObject = core::ptr::null_mut();
    v_res_3349_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(
            v_00_u03b2_3346_,
            v_m_3347_,
            v_a_3348_,
        );
    lean_dec_ref(v_a_3348_);
    lean_dec_ref(v_m_3347_);
    return v_res_3349_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(
    mut v_00_u03b1_3350_: *mut LeanObject,
    mut v_ref_3351_: *mut LeanObject,
    mut v_msg_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    v___x_3356_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(
        v_ref_3351_,
        v_msg_3352_,
        v___y_3353_,
        v___y_3354_,
    );
    return v___x_3356_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(
    mut v_00_u03b1_3357_: *mut LeanObject,
    mut v_ref_3358_: *mut LeanObject,
    mut v_msg_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3363_: *mut LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(
        v_00_u03b1_3357_,
        v_ref_3358_,
        v_msg_3359_,
        v___y_3360_,
        v___y_3361_,
    );
    lean_dec(v___y_3361_);
    lean_dec_ref(v___y_3360_);
    lean_dec(v_ref_3358_);
    return v_res_3363_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(
    mut v_upperBound_3364_: *mut LeanObject,
    mut v_snd_3365_: *mut LeanObject,
    mut v_fst_3366_: *mut LeanObject,
    mut v_inst_3367_: *mut LeanObject,
    mut v_R_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
    mut v_b_3370_: *mut LeanObject,
    mut v_c_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_upperBound_3376_: *mut LeanObject,
    mut v_snd_3377_: *mut LeanObject,
    mut v_fst_3378_: *mut LeanObject,
    mut v_inst_3379_: *mut LeanObject,
    mut v_R_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
    mut v_b_3382_: *mut LeanObject,
    mut v_c_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3385_);
    lean_dec_ref(v___y_3384_);
    lean_dec_ref(v_snd_3377_);
    lean_dec(v_upperBound_3376_);
    return v_res_3387_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(
    mut v_n_3388_: *mut LeanObject,
    mut v_as_3389_: *mut LeanObject,
    mut v_lo_3390_: *mut LeanObject,
    mut v_hi_3391_: *mut LeanObject,
    mut v_w_3392_: *mut LeanObject,
    mut v_hlo_3393_: *mut LeanObject,
    mut v_hhi_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    v___x_3395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_3388_, v_as_3389_, v_lo_3390_, v_hi_3391_);
    return v___x_3395_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(
    mut v_n_3396_: *mut LeanObject,
    mut v_as_3397_: *mut LeanObject,
    mut v_lo_3398_: *mut LeanObject,
    mut v_hi_3399_: *mut LeanObject,
    mut v_w_3400_: *mut LeanObject,
    mut v_hlo_3401_: *mut LeanObject,
    mut v_hhi_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3403_: *mut LeanObject = core::ptr::null_mut();
    v_res_3403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_3396_, v_as_3397_, v_lo_3398_, v_hi_3399_, v_w_3400_, v_hlo_3401_, v_hhi_3402_);
    lean_dec(v_hi_3399_);
    lean_dec(v_n_3396_);
    return v_res_3403_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(
    mut v_00_u03b2_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_x_3406_: *mut LeanObject,
) -> u8 {
    let mut v___x_3407_: u8 = 0;
    v___x_3407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_3405_, v_x_3406_);
    return v___x_3407_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(
    mut v_00_u03b2_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_x_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3411_: u8 = 0;
    let mut v_r_3412_: *mut LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_3408_, v_a_3409_, v_x_3410_);
    lean_dec(v_x_3410_);
    lean_dec_ref(v_a_3409_);
    v_r_3412_ = lean_box((v_res_3411_) as usize);
    return v_r_3412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(
    mut v_00_u03b2_3413_: *mut LeanObject,
    mut v_data_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(
    mut v_00_u03b2_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_b_3418_: *mut LeanObject,
    mut v_x_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    v___x_3420_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_3417_, v_b_3418_, v_x_3419_);
    return v___x_3420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(
    mut v_00_u03b2_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
    mut v_x_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_3422_, v_x_3423_);
    return v___x_3424_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(
    mut v_00_u03b2_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
    mut v_x_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3428_: *mut LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_3425_, v_a_3426_, v_x_3427_);
    lean_dec(v_x_3427_);
    lean_dec_ref(v_a_3426_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(
    mut v_msgData_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_3429_, v___y_3431_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(
    mut v_msgData_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3438_: *mut LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_3434_, v___y_3435_, v___y_3436_);
    lean_dec(v___y_3436_);
    lean_dec_ref(v___y_3435_);
    return v_res_3438_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(
    mut v_00_u03b1_3439_: *mut LeanObject,
    mut v_msg_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_3440_, v___y_3441_, v___y_3442_);
    return v___x_3444_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(
    mut v_00_u03b1_3445_: *mut LeanObject,
    mut v_msg_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3450_: *mut LeanObject = core::ptr::null_mut();
    v_res_3450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_3445_, v_msg_3446_, v___y_3447_, v___y_3448_);
    lean_dec(v___y_3448_);
    lean_dec_ref(v___y_3447_);
    return v_res_3450_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(
    mut v_00_u03b1_3451_: *mut LeanObject,
    mut v_msg_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_3452_, v___y_3453_, v___y_3454_);
    return v___x_3456_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(
    mut v_00_u03b1_3457_: *mut LeanObject,
    mut v_msg_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3462_: *mut LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_3457_, v_msg_3458_, v___y_3459_, v___y_3460_);
    lean_dec(v___y_3460_);
    lean_dec_ref(v___y_3459_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(
    mut v_00_u03b1_3463_: *mut LeanObject,
    mut v_preNode_3464_: *mut LeanObject,
    mut v_postNode_3465_: *mut LeanObject,
    mut v_x_3466_: *mut LeanObject,
    mut v_x_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    v___x_3471_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_3464_, v_postNode_3465_, v_x_3466_, v_x_3467_, v___y_3468_, v___y_3469_);
    return v___x_3471_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(
    mut v_00_u03b1_3472_: *mut LeanObject,
    mut v_preNode_3473_: *mut LeanObject,
    mut v_postNode_3474_: *mut LeanObject,
    mut v_x_3475_: *mut LeanObject,
    mut v_x_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_3472_, v_preNode_3473_, v_postNode_3474_, v_x_3475_, v_x_3476_, v___y_3477_, v___y_3478_);
    lean_dec(v___y_3478_);
    lean_dec_ref(v___y_3477_);
    return v_res_3480_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(
    mut v_n_3481_: *mut LeanObject,
    mut v_lo_3482_: *mut LeanObject,
    mut v_hi_3483_: *mut LeanObject,
    mut v_hhi_3484_: *mut LeanObject,
    mut v_pivot_3485_: *mut LeanObject,
    mut v_as_3486_: *mut LeanObject,
    mut v_i_3487_: *mut LeanObject,
    mut v_k_3488_: *mut LeanObject,
    mut v_ilo_3489_: *mut LeanObject,
    mut v_ik_3490_: *mut LeanObject,
    mut v_w_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_3483_, v_pivot_3485_, v_as_3486_, v_i_3487_, v_k_3488_);
    return v___x_3492_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(
    mut v_n_3493_: *mut LeanObject,
    mut v_lo_3494_: *mut LeanObject,
    mut v_hi_3495_: *mut LeanObject,
    mut v_hhi_3496_: *mut LeanObject,
    mut v_pivot_3497_: *mut LeanObject,
    mut v_as_3498_: *mut LeanObject,
    mut v_i_3499_: *mut LeanObject,
    mut v_k_3500_: *mut LeanObject,
    mut v_ilo_3501_: *mut LeanObject,
    mut v_ik_3502_: *mut LeanObject,
    mut v_w_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3504_: *mut LeanObject = core::ptr::null_mut();
    v_res_3504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_3493_, v_lo_3494_, v_hi_3495_, v_hhi_3496_, v_pivot_3497_, v_as_3498_, v_i_3499_, v_k_3500_, v_ilo_3501_, v_ik_3502_, v_w_3503_);
    lean_dec_ref(v_pivot_3497_);
    lean_dec(v_hi_3495_);
    lean_dec(v_lo_3494_);
    lean_dec(v_n_3493_);
    return v_res_3504_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3505_: *mut LeanObject,
    mut v_i_3506_: *mut LeanObject,
    mut v_source_3507_: *mut LeanObject,
    mut v_target_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    v___x_3509_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_3506_, v_source_3507_, v_target_3508_);
    return v___x_3509_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(
    mut v_msgData_3510_: *mut LeanObject,
    mut v_macroStack_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    v___x_3515_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_3510_, v_macroStack_3511_, v___y_3513_);
    return v___x_3515_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(
    mut v_msgData_3516_: *mut LeanObject,
    mut v_macroStack_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3521_: *mut LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_3516_, v_macroStack_3517_, v___y_3518_, v___y_3519_);
    lean_dec(v___y_3519_);
    lean_dec_ref(v___y_3518_);
    return v_res_3521_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(
    mut v_00_u03b1_3522_: *mut LeanObject,
    mut v_preNode_3523_: *mut LeanObject,
    mut v_postNode_3524_: *mut LeanObject,
    mut v___x_3525_: *mut LeanObject,
    mut v_x_3526_: *mut LeanObject,
    mut v_x_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_3523_, v_postNode_3524_, v___x_3525_, v_x_3526_, v_x_3527_, v___y_3528_, v___y_3529_);
    return v___x_3531_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(
    mut v_00_u03b1_3532_: *mut LeanObject,
    mut v_preNode_3533_: *mut LeanObject,
    mut v_postNode_3534_: *mut LeanObject,
    mut v___x_3535_: *mut LeanObject,
    mut v_x_3536_: *mut LeanObject,
    mut v_x_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_3532_, v_preNode_3533_, v_postNode_3534_, v___x_3535_, v_x_3536_, v_x_3537_, v___y_3538_, v___y_3539_);
    lean_dec(v___y_3539_);
    lean_dec_ref(v___y_3538_);
    return v_res_3541_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(
    mut v_00_u03b2_3542_: *mut LeanObject,
    mut v_x_3543_: *mut LeanObject,
    mut v_x_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    v___x_3545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_3543_, v_x_3544_);
    return v___x_3545_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_Linter_unusedSimpArgs;
    v___x_3548_ = l_Lean_Elab_Command_addLinter(v___x_3547_);
    return v___x_3548_;
}
pub unsafe fn l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(
    mut v_a_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3550_: *mut LeanObject = core::ptr::null_mut();
    v_res_3550_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
    return v_res_3550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_UnusedSimpArgs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_UnusedSimpArgs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_UnusedSimpArgs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_UnusedSimpArgs(builtin);
}
