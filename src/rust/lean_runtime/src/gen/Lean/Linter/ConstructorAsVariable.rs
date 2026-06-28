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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 78, 97, 109, 101, 65, 115, 86, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,2048112346130701713 as *mut LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanStringObject<85> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 108, 105, 110, 116, 101, 114, 32, 116, 104, 97, 116, 32, 119, 97, 114, 110, 115, 32, 119, 104, 101, 110, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110, 97, 109, 101, 115, 32, 97, 114, 101, 32, 110, 117, 108, 108, 97, 114, 121, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,3378770564748755370 as *mut LeanObject] };
static mut l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [76, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 114, 101, 115, 101, 109, 98, 108, 101, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [39, 32, 45, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [119, 114, 105, 116, 101, 32, 39, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [39, 32, 40, 119, 105, 116, 104, 32, 97, 32, 100, 111, 116, 41, 32, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 116, 111, 32, 117, 115, 101, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_constructorNameAsVariable___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_constructorNameAsVariable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_constructorNameAsVariable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__0_value)
        as *mut LeanObject;
static l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l_Lean_Linter_constructorNameAsVariable___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value) as *mut LeanObject,18151959854494862315 as *mut LeanObject] };
static mut l_Lean_Linter_constructorNameAsVariable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_constructorNameAsVariable___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_constructorNameAsVariable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_constructorNameAsVariable: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_constructorNameAsVariable___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(
    mut v_name_1592_: *mut LeanObject,
    mut v_decl_1593_: *mut LeanObject,
    mut v_ref_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut v_unused_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1596_ = lean_ctor_get(v_decl_1593_, 0);
                v_descr_1597_ = lean_ctor_get(v_decl_1593_, 1);
                v_deprecation_x3f_1598_ = lean_ctor_get(v_decl_1593_, 2);
                v___x_1599_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1600_ = (lean_unbox(v_defValue_1596_) as u8);
                lean_ctor_set_uint8(v___x_1599_, 0 as u32, v___x_1600_);
                lean_inc(v_deprecation_x3f_1598_);
                lean_inc_ref(v_descr_1597_);
                lean_inc_n(v_name_1592_, 2);
                v___x_1601_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1601_, 0, v_name_1592_);
                lean_ctor_set(v___x_1601_, 1, v_ref_1594_);
                lean_ctor_set(v___x_1601_, 2, v___x_1599_);
                lean_ctor_set(v___x_1601_, 3, v_descr_1597_);
                lean_ctor_set(v___x_1601_, 4, v_deprecation_x3f_1598_);
                v___x_1602_ = lean_register_option(v_name_1592_, v___x_1601_);
                if lean_obj_tag(v___x_1602_) == 0 {
                    v_isSharedCheck_1610_ = (!lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1610_ == 0 {
                        v_unused_1611_ = lean_ctor_get(v___x_1602_, 0);
                        lean_dec(v_unused_1611_);
                        v___x_1604_ = v___x_1602_;
                        v_isShared_1605_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1602_);
                        v___x_1604_ = lean_box(0);
                        v_isShared_1605_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1592_);
                    v_a_1612_ = lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1619_ = (!lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1614_ = v___x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1612_);
                        lean_dec(v___x_1602_);
                        v___x_1614_ = lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1596_);
                v___x_1606_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1606_, 0, v_name_1592_);
                lean_ctor_set(v___x_1606_, 1, v_defValue_1596_);
                if v_isShared_1605_ == 0 {
                    lean_ctor_set(v___x_1604_, 0, v___x_1606_);
                    v___x_1608_ = v___x_1604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
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
                    v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
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
    mut v_name_1620_: *mut LeanObject,
    mut v_decl_1621_: *mut LeanObject,
    mut v_ref_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v_name_1620_, v_decl_1621_, v_ref_1622_);
    lean_dec_ref(v_decl_1621_);
    return v_res_1624_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1645_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1646_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
    v___x_1647_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v___x_1644_, v___x_1645_, v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(
    mut v_a_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1649_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
    return v_res_1649_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(
    mut v_o_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1653_ = lean_st_ref_get(v___y_1651_);
    v_env_1654_ = lean_ctor_get(v___x_1653_, 0);
    lean_inc_ref(v_env_1654_);
    lean_dec(v___x_1653_);
    v___x_1655_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_1656_ = lean_ctor_get(v___x_1655_, 0);
    v_asyncMode_1657_ = lean_ctor_get(v_toEnvExtension_1656_, 2);
    v___x_1658_ = lean_box(1);
    v___x_1659_ = lean_box(0);
    v_linterSets_1660_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1658_,
        v___x_1655_,
        v_env_1654_,
        v_asyncMode_1657_,
        v___x_1659_,
    );
    v___x_1661_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1661_, 0, v_o_1650_);
    lean_ctor_set(v___x_1661_, 1, v_linterSets_1660_);
    v___x_1662_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(
    mut v_o_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1666_: *mut LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_1663_, v___y_1664_);
    lean_dec(v___y_1664_);
    return v_res_1666_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(
    mut v_o_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_1667_, v___y_1669_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(
    mut v_o_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1676_: *mut LeanObject = core::ptr::null_mut();
    v_res_1676_ =
        l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(
            v_o_1672_,
            v___y_1673_,
            v___y_1674_,
        );
    lean_dec(v___y_1674_);
    lean_dec_ref(v___y_1673_);
    return v_res_1676_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
    mut v_e_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut v_unused_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1680_ = l_Lean_Expr_hasMVar(v_e_1677_);
                if v___x_1680_ == 0 {
                    v___x_1681_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1681_, 0, v_e_1677_);
                    return v___x_1681_;
                } else {
                    v___x_1682_ = lean_st_ref_get(v___y_1678_);
                    v_mctx_1683_ = lean_ctor_get(v___x_1682_, 0);
                    lean_inc_ref(v_mctx_1683_);
                    lean_dec(v___x_1682_);
                    v___x_1684_ = l_Lean_instantiateMVarsCore(v_mctx_1683_, v_e_1677_);
                    v_fst_1685_ = lean_ctor_get(v___x_1684_, 0);
                    lean_inc(v_fst_1685_);
                    v_snd_1686_ = lean_ctor_get(v___x_1684_, 1);
                    lean_inc(v_snd_1686_);
                    lean_dec_ref(v___x_1684_);
                    v___x_1687_ = lean_st_ref_take(v___y_1678_);
                    v_cache_1688_ = lean_ctor_get(v___x_1687_, 1);
                    v_zetaDeltaFVarIds_1689_ = lean_ctor_get(v___x_1687_, 2);
                    v_postponed_1690_ = lean_ctor_get(v___x_1687_, 3);
                    v_diag_1691_ = lean_ctor_get(v___x_1687_, 4);
                    v_isSharedCheck_1700_ = (!lean_is_exclusive(v___x_1687_)) as u8;
                    if v_isSharedCheck_1700_ == 0 {
                        v_unused_1701_ = lean_ctor_get(v___x_1687_, 0);
                        lean_dec(v_unused_1701_);
                        v___x_1693_ = v___x_1687_;
                        v_isShared_1694_ = v_isSharedCheck_1700_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1691_);
                        lean_inc(v_postponed_1690_);
                        lean_inc(v_zetaDeltaFVarIds_1689_);
                        lean_inc(v_cache_1688_);
                        lean_dec(v___x_1687_);
                        v___x_1693_ = lean_box(0);
                        v_isShared_1694_ = v_isSharedCheck_1700_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1694_ == 0 {
                    lean_ctor_set(v___x_1693_, 0, v_snd_1686_);
                    v___x_1696_ = v___x_1693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_snd_1686_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_cache_1688_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_zetaDeltaFVarIds_1689_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_postponed_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_diag_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1697_ = lean_st_ref_set(v___y_1678_, v___x_1696_);
                v___x_1698_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1698_, 0, v_fst_1685_);
                return v___x_1698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(
    mut v_e_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1705_: *mut LeanObject = core::ptr::null_mut();
    v_res_1705_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_e_1702_,
            v___y_1703_,
        );
    lean_dec(v___y_1703_);
    return v_res_1705_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(
    mut v_e_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    v___x_1712_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_e_1706_,
            v___y_1708_,
        );
    return v___x_1712_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(
    mut v_e_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_res_1719_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(
        v_e_1713_,
        v___y_1714_,
        v___y_1715_,
        v___y_1716_,
        v___y_1717_,
    );
    lean_dec(v___y_1717_);
    lean_dec_ref(v___y_1716_);
    lean_dec(v___y_1715_);
    lean_dec_ref(v___y_1714_);
    return v_res_1719_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(
    mut v_hi_1720_: *mut LeanObject,
    mut v_pivot_1721_: *mut LeanObject,
    mut v_as_1722_: *mut LeanObject,
    mut v_i_1723_: *mut LeanObject,
    mut v_k_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1725_ = lean_nat_dec_lt(v_k_1724_, v_hi_1720_);
                if v___x_1725_ == 0 {
                    lean_dec(v_k_1724_);
                    v___x_1726_ = lean_array_fswap(v_as_1722_, v_i_1723_, v_hi_1720_);
                    v___x_1727_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1727_, 0, v_i_1723_);
                    lean_ctor_set(v___x_1727_, 1, v___x_1726_);
                    return v___x_1727_;
                } else {
                    v___x_1728_ = lean_array_fget_borrowed(v_as_1722_, v_k_1724_);
                    v_fst_1729_ = lean_ctor_get(v___x_1728_, 0);
                    v_fst_1730_ = lean_ctor_get(v_pivot_1721_, 0);
                    v_start_1731_ = lean_ctor_get(v_fst_1729_, 0);
                    v_start_1732_ = lean_ctor_get(v_fst_1730_, 0);
                    v___x_1733_ = lean_nat_dec_lt(v_start_1731_, v_start_1732_);
                    if v___x_1733_ == 0 {
                        v___x_1734_ = lean_unsigned_to_nat(1);
                        v___x_1735_ = lean_nat_add(v_k_1724_, v___x_1734_);
                        lean_dec(v_k_1724_);
                        v_k_1724_ = v___x_1735_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1737_ = lean_array_fswap(v_as_1722_, v_i_1723_, v_k_1724_);
                        v___x_1738_ = lean_unsigned_to_nat(1);
                        v___x_1739_ = lean_nat_add(v_i_1723_, v___x_1738_);
                        lean_dec(v_i_1723_);
                        v___x_1740_ = lean_nat_add(v_k_1724_, v___x_1738_);
                        lean_dec(v_k_1724_);
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
    mut v_hi_1742_: *mut LeanObject,
    mut v_pivot_1743_: *mut LeanObject,
    mut v_as_1744_: *mut LeanObject,
    mut v_i_1745_: *mut LeanObject,
    mut v_k_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1747_: *mut LeanObject = core::ptr::null_mut();
    v_res_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1742_, v_pivot_1743_, v_as_1744_, v_i_1745_, v_k_1746_);
    lean_dec_ref(v_pivot_1743_);
    lean_dec(v_hi_1742_);
    return v_res_1747_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(
    mut v_x1_1748_: *mut LeanObject,
    mut v_x2_1749_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    v_fst_1750_ = lean_ctor_get(v_x1_1748_, 0);
    v_fst_1751_ = lean_ctor_get(v_x2_1749_, 0);
    v_start_1752_ = lean_ctor_get(v_fst_1750_, 0);
    v_start_1753_ = lean_ctor_get(v_fst_1751_, 0);
    v___x_1754_ = lean_nat_dec_lt(v_start_1752_, v_start_1753_);
    return v___x_1754_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(
    mut v_x1_1755_: *mut LeanObject,
    mut v_x2_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1757_: u8 = 0;
    let mut v_r_1758_: *mut LeanObject = core::ptr::null_mut();
    v_res_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_1755_, v_x2_1756_);
    lean_dec_ref(v_x2_1756_);
    lean_dec_ref(v_x1_1755_);
    v_r_1758_ = lean_box((v_res_1757_) as usize);
    return v_r_1758_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(
    mut v_n_1759_: *mut LeanObject,
    mut v_as_1760_: *mut LeanObject,
    mut v_lo_1761_: *mut LeanObject,
    mut v_hi_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1774_ = lean_nat_dec_lt(v_lo_1761_, v_hi_1762_);
                if v___x_1774_ == 0 {
                    lean_dec(v_lo_1761_);
                    return v_as_1760_;
                } else {
                    v___x_1775_ = lean_nat_add(v_lo_1761_, v_hi_1762_);
                    v___x_1776_ = lean_unsigned_to_nat(1);
                    v_mid_1777_ = lean_nat_shiftr(v___x_1775_, v___x_1776_);
                    lean_dec(v___x_1775_);
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
                lean_inc_n(v_lo_1761_, 2);
                v___x_1766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1762_, v_pivot_1765_, v___y_1764_, v_lo_1761_, v_lo_1761_);
                lean_dec(v_pivot_1765_);
                v_fst_1767_ = lean_ctor_get(v___x_1766_, 0);
                lean_inc(v_fst_1767_);
                v_snd_1768_ = lean_ctor_get(v___x_1766_, 1);
                lean_inc(v_snd_1768_);
                lean_dec_ref(v___x_1766_);
                v___x_1769_ = lean_nat_dec_le(v_hi_1762_, v_fst_1767_);
                if v___x_1769_ == 0 {
                    v___x_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1759_, v_snd_1768_, v_lo_1761_, v_fst_1767_);
                    v___x_1771_ = lean_unsigned_to_nat(1);
                    v___x_1772_ = lean_nat_add(v_fst_1767_, v___x_1771_);
                    lean_dec(v_fst_1767_);
                    v_as_1760_ = v___x_1770_;
                    v_lo_1761_ = v___x_1772_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_1767_);
                    lean_dec(v_lo_1761_);
                    return v_snd_1768_;
                }
            }
            2 => {
                v___x_1780_ = lean_array_fget_borrowed(v___y_1779_, v_mid_1777_);
                v___x_1781_ = lean_array_fget_borrowed(v___y_1779_, v_hi_1762_);
                v___x_1782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_1780_, v___x_1781_);
                if v___x_1782_ == 0 {
                    lean_dec(v_mid_1777_);
                    v___y_1764_ = v___y_1779_;
                    state = 1;
                    continue;
                } else {
                    v___x_1783_ = lean_array_fswap(v___y_1779_, v_mid_1777_, v_hi_1762_);
                    lean_dec(v_mid_1777_);
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
    mut v_n_1794_: *mut LeanObject,
    mut v_as_1795_: *mut LeanObject,
    mut v_lo_1796_: *mut LeanObject,
    mut v_hi_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1794_, v_as_1795_, v_lo_1796_, v_hi_1797_);
    lean_dec(v_hi_1797_);
    lean_dec(v_n_1794_);
    return v_res_1798_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(
    mut v___y_1800_: u8,
    mut v_suppressElabErrors_1801_: u8,
    mut v_x_1802_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1802_) == 1 {
        let mut v_pre_1803_: *mut LeanObject = core::ptr::null_mut();
        v_pre_1803_ = lean_ctor_get(v_x_1802_, 0);
        if lean_obj_tag(v_pre_1803_) == 0 {
            let mut v_str_1804_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1806_: u8 = 0;
            v_str_1804_ = lean_ctor_get(v_x_1802_, 1);
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
    mut v___y_1807_: *mut LeanObject,
    mut v_suppressElabErrors_1808_: *mut LeanObject,
    mut v_x_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21688__boxed_1810_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1811_: u8 = 0;
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut LeanObject = core::ptr::null_mut();
    v___y_21688__boxed_1810_ = (lean_unbox(v___y_1807_) as u8);
    v_suppressElabErrors_boxed_1811_ = (lean_unbox(v_suppressElabErrors_1808_) as u8);
    v_res_1812_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21688__boxed_1810_, v_suppressElabErrors_boxed_1811_, v_x_1809_);
    lean_dec(v_x_1809_);
    v_r_1813_ = lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(
    mut v_opts_1814_: *mut LeanObject,
    mut v_opt_1815_: *mut LeanObject,
) -> u8 {
    let mut v_name_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    v_name_1816_ = lean_ctor_get(v_opt_1815_, 0);
    v_defValue_1817_ = lean_ctor_get(v_opt_1815_, 1);
    v_map_1818_ = lean_ctor_get(v_opts_1814_, 0);
    v___x_1819_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1818_,
            v_name_1816_,
        );
    if lean_obj_tag(v___x_1819_) == 0 {
        let mut v___x_1820_: u8 = 0;
        v___x_1820_ = (lean_unbox(v_defValue_1817_) as u8);
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut LeanObject = core::ptr::null_mut();
        v_val_1821_ = lean_ctor_get(v___x_1819_, 0);
        lean_inc(v_val_1821_);
        lean_dec_ref_known(v___x_1819_, 1);
        if lean_obj_tag(v_val_1821_) == 1 {
            let mut v_v_1822_: u8 = 0;
            v_v_1822_ = lean_ctor_get_uint8(v_val_1821_, 0 as u32);
            lean_dec_ref_known(v_val_1821_, 0);
            return v_v_1822_;
        } else {
            let mut v___x_1823_: u8 = 0;
            lean_dec(v_val_1821_);
            v___x_1823_ = (lean_unbox(v_defValue_1817_) as u8);
            return v___x_1823_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(
    mut v_opts_1824_: *mut LeanObject,
    mut v_opt_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1826_: u8 = 0;
    let mut v_r_1827_: *mut LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_1824_, v_opt_1825_);
    lean_dec_ref(v_opt_1825_);
    lean_dec_ref(v_opts_1824_);
    v_r_1827_ = lean_box((v_res_1826_) as usize);
    return v_r_1827_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1828_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    v___x_1829_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
    v___x_1830_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1830_, 0, v___x_1829_);
    return v___x_1830_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
    v___x_1832_ = lean_unsigned_to_nat(0);
    v___x_1833_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1833_, 0, v___x_1832_);
    lean_ctor_set(v___x_1833_, 1, v___x_1832_);
    lean_ctor_set(v___x_1833_, 2, v___x_1832_);
    lean_ctor_set(v___x_1833_, 3, v___x_1832_);
    lean_ctor_set(v___x_1833_, 4, v___x_1831_);
    lean_ctor_set(v___x_1833_, 5, v___x_1831_);
    lean_ctor_set(v___x_1833_, 6, v___x_1831_);
    lean_ctor_set(v___x_1833_, 7, v___x_1831_);
    lean_ctor_set(v___x_1833_, 8, v___x_1831_);
    lean_ctor_set(v___x_1833_, 9, v___x_1831_);
    return v___x_1833_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = lean_unsigned_to_nat(32);
    v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
    v___x_1836_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1836_, 0, v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    v___x_1837_ = 5usize;
    v___x_1838_ = lean_unsigned_to_nat(0);
    v___x_1839_ = lean_unsigned_to_nat(32);
    v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1839_);
    v___x_1841_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
    v___x_1842_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    lean_ctor_set(v___x_1842_, 2, v___x_1838_);
    lean_ctor_set(v___x_1842_, 3, v___x_1838_);
    lean_ctor_set_usize(v___x_1842_, 4, v___x_1837_);
    return v___x_1842_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = lean_box(1);
    v___x_1844_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
    v___x_1845_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
    v___x_1846_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1846_, 0, v___x_1845_);
    lean_ctor_set(v___x_1846_, 1, v___x_1844_);
    lean_ctor_set(v___x_1846_, 2, v___x_1843_);
    return v___x_1846_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(
    mut v_msgData_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    v___x_1850_ = lean_st_ref_get(v___y_1848_);
    v_env_1851_ = lean_ctor_get(v___x_1850_, 0);
    lean_inc_ref(v_env_1851_);
    lean_dec(v___x_1850_);
    v___x_1852_ = lean_st_ref_get(v___y_1848_);
    v_scopes_1853_ = lean_ctor_get(v___x_1852_, 2);
    lean_inc(v_scopes_1853_);
    lean_dec(v___x_1852_);
    v___x_1854_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1855_ = l_List_head_x21___redArg(v___x_1854_, v_scopes_1853_);
    lean_dec(v_scopes_1853_);
    v_opts_1856_ = lean_ctor_get(v___x_1855_, 1);
    lean_inc_ref(v_opts_1856_);
    lean_dec(v___x_1855_);
    v___x_1857_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
    v___x_1858_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
    v___x_1859_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1859_, 0, v_env_1851_);
    lean_ctor_set(v___x_1859_, 1, v___x_1857_);
    lean_ctor_set(v___x_1859_, 2, v___x_1858_);
    lean_ctor_set(v___x_1859_, 3, v_opts_1856_);
    v___x_1860_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    lean_ctor_set(v___x_1860_, 1, v_msgData_1847_);
    v___x_1861_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1861_, 0, v___x_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(
    mut v_msgData_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1865_: *mut LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1862_, v___y_1863_);
    lean_dec(v___y_1863_);
    return v_res_1865_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(
    mut v_ref_1867_: *mut LeanObject,
    mut v_msgData_1868_: *mut LeanObject,
    mut v_severity_1869_: u8,
    mut v_isSilent_1870_: u8,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: u8 = 0;
    let mut v___y_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: u8 = 0;
    let mut v___y_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v_a_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v_a_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v___y_1938_: u8 = 0;
    let mut v___y_1939_: u8 = 0;
    let mut v___y_1940_: u8 = 0;
    let mut v___y_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1945_: u8 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v___y_1966_: u8 = 0;
    let mut v___y_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: u8 = 0;
    let mut v___y_1969_: u8 = 0;
    let mut v___y_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: u8 = 0;
    let mut v___y_1975_: u8 = 0;
    let mut v___y_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v___x_1991_: u8 = 0;
    let mut v___y_1993_: u8 = 0;
    let mut v___y_1994_: u8 = 0;
    let mut v___y_1995_: u8 = 0;
    let mut v___y_1997_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_1868_);
                    v___x_2010_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1868_);
                    v___y_1997_ = v___x_2010_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1883_ = l_Lean_Elab_Command_getScope___redArg(v___y_1882_);
                if lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                    lean_inc(v_a_1884_);
                    lean_dec_ref_known(v___x_1883_, 1);
                    v___x_1885_ = l_Lean_Elab_Command_getScope___redArg(v___y_1882_);
                    if lean_obj_tag(v___x_1885_) == 0 {
                        v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
                        v_isSharedCheck_1920_ = (!lean_is_exclusive(v___x_1885_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1888_ = v___x_1885_;
                            v_isShared_1889_ = v_isSharedCheck_1920_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1886_);
                            lean_dec(v___x_1885_);
                            v___x_1888_ = lean_box(0);
                            v_isShared_1889_ = v_isSharedCheck_1920_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1884_);
                        lean_dec(v___y_1880_);
                        lean_dec_ref(v___y_1878_);
                        lean_dec_ref(v___y_1876_);
                        v_a_1921_ = lean_ctor_get(v___x_1885_, 0);
                        v_isSharedCheck_1928_ = (!lean_is_exclusive(v___x_1885_)) as u8;
                        if v_isSharedCheck_1928_ == 0 {
                            v___x_1923_ = v___x_1885_;
                            v_isShared_1924_ = v_isSharedCheck_1928_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1921_);
                            lean_dec(v___x_1885_);
                            v___x_1923_ = lean_box(0);
                            v_isShared_1924_ = v_isSharedCheck_1928_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1880_);
                    lean_dec_ref(v___y_1878_);
                    lean_dec_ref(v___y_1876_);
                    v_a_1929_ = lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1936_ = (!lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1931_ = v___x_1883_;
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1929_);
                        lean_dec(v___x_1883_);
                        v___x_1931_ = lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1890_ = lean_st_ref_take(v___y_1882_);
                v_currNamespace_1891_ = lean_ctor_get(v_a_1884_, 2);
                lean_inc(v_currNamespace_1891_);
                lean_dec(v_a_1884_);
                v_openDecls_1892_ = lean_ctor_get(v_a_1886_, 3);
                lean_inc(v_openDecls_1892_);
                lean_dec(v_a_1886_);
                v_env_1893_ = lean_ctor_get(v___x_1890_, 0);
                v_messages_1894_ = lean_ctor_get(v___x_1890_, 1);
                v_scopes_1895_ = lean_ctor_get(v___x_1890_, 2);
                v_usedQuotCtxts_1896_ = lean_ctor_get(v___x_1890_, 3);
                v_nextMacroScope_1897_ = lean_ctor_get(v___x_1890_, 4);
                v_maxRecDepth_1898_ = lean_ctor_get(v___x_1890_, 5);
                v_ngen_1899_ = lean_ctor_get(v___x_1890_, 6);
                v_auxDeclNGen_1900_ = lean_ctor_get(v___x_1890_, 7);
                v_infoState_1901_ = lean_ctor_get(v___x_1890_, 8);
                v_traceState_1902_ = lean_ctor_get(v___x_1890_, 9);
                v_snapshotTasks_1903_ = lean_ctor_get(v___x_1890_, 10);
                v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1890_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1905_ = v___x_1890_;
                    v_isShared_1906_ = v_isSharedCheck_1919_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1903_);
                    lean_inc(v_traceState_1902_);
                    lean_inc(v_infoState_1901_);
                    lean_inc(v_auxDeclNGen_1900_);
                    lean_inc(v_ngen_1899_);
                    lean_inc(v_maxRecDepth_1898_);
                    lean_inc(v_nextMacroScope_1897_);
                    lean_inc(v_usedQuotCtxts_1896_);
                    lean_inc(v_scopes_1895_);
                    lean_inc(v_messages_1894_);
                    lean_inc(v_env_1893_);
                    lean_dec(v___x_1890_);
                    v___x_1905_ = lean_box(0);
                    v_isShared_1906_ = v_isSharedCheck_1919_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1907_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v_currNamespace_1891_);
                lean_ctor_set(v___x_1907_, 1, v_openDecls_1892_);
                v___x_1908_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1908_, 0, v___x_1907_);
                lean_ctor_set(v___x_1908_, 1, v___y_1878_);
                lean_inc_ref(v___y_1875_);
                lean_inc_ref(v___y_1877_);
                v___x_1909_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_1909_, 0, v___y_1877_);
                lean_ctor_set(v___x_1909_, 1, v___y_1876_);
                lean_ctor_set(v___x_1909_, 2, v___y_1880_);
                lean_ctor_set(v___x_1909_, 3, v___y_1875_);
                lean_ctor_set(v___x_1909_, 4, v___x_1908_);
                lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_1879_,
                );
                lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_1881_,
                );
                lean_ctor_set_uint8(
                    v___x_1909_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1870_,
                );
                v___x_1910_ = l_Lean_MessageLog_add(v___x_1909_, v_messages_1894_);
                if v_isShared_1906_ == 0 {
                    lean_ctor_set(v___x_1905_, 1, v___x_1910_);
                    v___x_1912_ = v___x_1905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1893_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1910_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_scopes_1895_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_usedQuotCtxts_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_nextMacroScope_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_maxRecDepth_1898_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_ngen_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_auxDeclNGen_1900_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_infoState_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 9, v_traceState_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 10, v_snapshotTasks_1903_);
                    v___x_1912_ = v_reuseFailAlloc_1918_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1913_ = lean_st_ref_set(v___y_1882_, v___x_1912_);
                v___x_1914_ = lean_box(0);
                if v_isShared_1889_ == 0 {
                    lean_ctor_set(v___x_1888_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1888_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
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
                    v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
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
                    v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
                    v___x_1934_ = v_reuseFailAlloc_1935_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1934_;
            }
            10 => {
                v_fileName_1943_ = lean_ctor_get(v___y_1871_, 0);
                v_fileMap_1944_ = lean_ctor_get(v___y_1871_, 1);
                v_suppressElabErrors_1945_ = lean_ctor_get_uint8(
                    v___y_1871_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_1946_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1868_,
                    );
                v___x_1947_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_1946_, v___y_1872_);
                v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
                v_isSharedCheck_1964_ = (!lean_is_exclusive(v___x_1947_)) as u8;
                if v_isSharedCheck_1964_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    v_isShared_1951_ = v_isSharedCheck_1964_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_1948_);
                    lean_dec(v___x_1947_);
                    v___x_1950_ = lean_box(0);
                    v_isShared_1951_ = v_isSharedCheck_1964_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_1944_, 2);
                v___x_1952_ = l_Lean_FileMap_toPosition(v_fileMap_1944_, v___y_1941_);
                lean_dec(v___y_1941_);
                v___x_1953_ = l_Lean_FileMap_toPosition(v_fileMap_1944_, v___y_1942_);
                lean_dec(v___y_1942_);
                v___x_1954_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                v___x_1955_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0;
                if v_suppressElabErrors_1945_ == 0 {
                    lean_del_object(v___x_1950_);
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
                    v___x_1956_ = lean_box((v___y_1938_) as usize);
                    v___x_1957_ = lean_box((v_suppressElabErrors_1945_) as usize);
                    v___f_1958_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_1958_, 0, v___x_1956_);
                    lean_closure_set(v___f_1958_, 1, v___x_1957_);
                    lean_inc(v_a_1948_);
                    v___x_1959_ = l_Lean_MessageData_hasTag(v___f_1958_, v_a_1948_);
                    if v___x_1959_ == 0 {
                        lean_dec_ref_known(v___x_1954_, 1);
                        lean_dec_ref(v___x_1952_);
                        lean_dec(v_a_1948_);
                        v___x_1960_ = lean_box(0);
                        if v_isShared_1951_ == 0 {
                            lean_ctor_set(v___x_1950_, 0, v___x_1960_);
                            v___x_1962_ = v___x_1950_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
                            v___x_1962_ = v_reuseFailAlloc_1963_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1950_);
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
                lean_dec(v___y_1967_);
                if lean_obj_tag(v___x_1971_) == 0 {
                    lean_inc(v___y_1970_);
                    v___y_1938_ = v___y_1966_;
                    v___y_1939_ = v___y_1968_;
                    v___y_1940_ = v___y_1969_;
                    v___y_1941_ = v___y_1970_;
                    v___y_1942_ = v___y_1970_;
                    state = 10;
                    continue;
                } else {
                    v_val_1972_ = lean_ctor_get(v___x_1971_, 0);
                    lean_inc(v_val_1972_);
                    lean_dec_ref_known(v___x_1971_, 1);
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
                if lean_obj_tag(v___x_1977_) == 0 {
                    v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
                    lean_inc(v_a_1978_);
                    lean_dec_ref_known(v___x_1977_, 1);
                    v_ref_1979_ = l_Lean_replaceRef(v_ref_1867_, v_a_1978_);
                    lean_dec(v_a_1978_);
                    v___x_1980_ = l_Lean_Syntax_getPos_x3f(v_ref_1979_, v___y_1975_);
                    if lean_obj_tag(v___x_1980_) == 0 {
                        v___x_1981_ = lean_unsigned_to_nat(0);
                        v___y_1966_ = v___y_1974_;
                        v___y_1967_ = v_ref_1979_;
                        v___y_1968_ = v___y_1975_;
                        v___y_1969_ = v___y_1976_;
                        v___y_1970_ = v___x_1981_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1982_ = lean_ctor_get(v___x_1980_, 0);
                        lean_inc(v_val_1982_);
                        lean_dec_ref_known(v___x_1980_, 1);
                        v___y_1966_ = v___y_1974_;
                        v___y_1967_ = v_ref_1979_;
                        v___y_1968_ = v___y_1975_;
                        v___y_1969_ = v___y_1976_;
                        v___y_1970_ = v_val_1982_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1868_);
                    v_a_1983_ = lean_ctor_get(v___x_1977_, 0);
                    v_isSharedCheck_1990_ = (!lean_is_exclusive(v___x_1977_)) as u8;
                    if v_isSharedCheck_1990_ == 0 {
                        v___x_1985_ = v___x_1977_;
                        v_isShared_1986_ = v_isSharedCheck_1990_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1983_);
                        lean_dec(v___x_1977_);
                        v___x_1985_ = lean_box(0);
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
                    v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
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
                    v_scopes_1999_ = lean_ctor_get(v___x_1998_, 2);
                    lean_inc(v_scopes_1999_);
                    lean_dec(v___x_1998_);
                    v___x_2000_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2001_ = l_List_head_x21___redArg(v___x_2000_, v_scopes_1999_);
                    lean_dec(v_scopes_1999_);
                    v_opts_2002_ = lean_ctor_get(v___x_2001_, 1);
                    lean_inc_ref(v_opts_2002_);
                    lean_dec(v___x_2001_);
                    v___x_2003_ = 1;
                    v___x_2004_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1869_, v___x_2003_);
                    if v___x_2004_ == 0 {
                        lean_dec_ref(v_opts_2002_);
                        v___y_1993_ = v___y_1997_;
                        v___y_1994_ = v___y_1997_;
                        v___y_1995_ = v___x_2004_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2005_ = l_Lean_warningAsError;
                        v___x_2006_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_2002_, v___x_2005_);
                        lean_dec_ref(v_opts_2002_);
                        v___y_1993_ = v___y_1997_;
                        v___y_1994_ = v___y_1997_;
                        v___y_1995_ = v___x_2006_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1868_);
                    v___x_2007_ = lean_box(0);
                    v___x_2008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2008_, 0, v___x_2007_);
                    return v___x_2008_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(
    mut v_ref_2011_: *mut LeanObject,
    mut v_msgData_2012_: *mut LeanObject,
    mut v_severity_2013_: *mut LeanObject,
    mut v_isSilent_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2018_: u8 = 0;
    let mut v_isSilent_boxed_2019_: u8 = 0;
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2018_ = (lean_unbox(v_severity_2013_) as u8);
    v_isSilent_boxed_2019_ = (lean_unbox(v_isSilent_2014_) as u8);
    v_res_2020_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_2011_, v_msgData_2012_, v_severity_boxed_2018_, v_isSilent_boxed_2019_, v___y_2015_, v___y_2016_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v___y_2015_);
    lean_dec(v_ref_2011_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(
    mut v_ref_2021_: *mut LeanObject,
    mut v_msgData_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    v___x_2026_ = 1;
    v___x_2027_ = 0;
    v___x_2028_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_2021_, v_msgData_2022_, v___x_2026_, v___x_2027_, v___y_2023_, v___y_2024_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(
    mut v_ref_2029_: *mut LeanObject,
    mut v_msgData_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2034_: *mut LeanObject = core::ptr::null_mut();
    v_res_2034_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_2029_, v_msgData_2030_, v___y_2031_, v___y_2032_);
    lean_dec(v___y_2032_);
    lean_dec_ref(v___y_2031_);
    lean_dec(v_ref_2029_);
    return v_res_2034_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1()
-> *mut LeanObject {
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    v___x_2036_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0;
    v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3()
-> *mut LeanObject {
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    v___x_2039_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2;
    v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
    return v___x_2040_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
    mut v_linterOption_2041_: *mut LeanObject,
    mut v_stx_2042_: *mut LeanObject,
    mut v_msg_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_unused_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2047_ = lean_ctor_get(v_linterOption_2041_, 0);
                v_isSharedCheck_2064_ = (!lean_is_exclusive(v_linterOption_2041_)) as u8;
                if v_isSharedCheck_2064_ == 0 {
                    v_unused_2065_ = lean_ctor_get(v_linterOption_2041_, 1);
                    lean_dec(v_unused_2065_);
                    v___x_2049_ = v_linterOption_2041_;
                    v_isShared_2050_ = v_isSharedCheck_2064_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2047_);
                    lean_dec(v_linterOption_2041_);
                    v___x_2049_ = lean_box(0);
                    v_isShared_2050_ = v_isSharedCheck_2064_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2051_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
                lean_inc(v_name_2047_);
                v___x_2052_ = l_Lean_MessageData_ofName(v_name_2047_);
                if v_isShared_2050_ == 0 {
                    lean_ctor_set_tag(v___x_2049_, 7);
                    lean_ctor_set(v___x_2049_, 1, v___x_2052_);
                    lean_ctor_set(v___x_2049_, 0, v___x_2051_);
                    v___x_2054_ = v___x_2049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2051_);
                    lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2052_);
                    v___x_2054_ = v_reuseFailAlloc_2063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2055_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
                v___x_2056_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2056_, 0, v___x_2054_);
                lean_ctor_set(v___x_2056_, 1, v___x_2055_);
                v_disable_2057_ = l_Lean_MessageData_note(v___x_2056_);
                v___x_2058_ = l_Lean_Linter_linterMessageTag;
                v___x_2059_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2059_, 0, v_msg_2043_);
                lean_ctor_set(v___x_2059_, 1, v_disable_2057_);
                v___x_2060_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2060_, 0, v___x_2058_);
                lean_ctor_set(v___x_2060_, 1, v___x_2059_);
                v___x_2061_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v_name_2047_);
                lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                v___x_2062_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_2042_, v___x_2061_, v___y_2044_, v___y_2045_);
                return v___x_2062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(
    mut v_linterOption_2066_: *mut LeanObject,
    mut v_stx_2067_: *mut LeanObject,
    mut v_msg_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2072_: *mut LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
        v_linterOption_2066_,
        v_stx_2067_,
        v_msg_2068_,
        v___y_2069_,
        v___y_2070_,
    );
    lean_dec(v___y_2070_);
    lean_dec_ref(v___y_2069_);
    lean_dec(v_stx_2067_);
    return v_res_2072_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1()
-> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0;
    v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3()
-> *mut LeanObject {
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2;
    v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
    return v___x_2078_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5()
-> *mut LeanObject {
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4;
    v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
    return v___x_2081_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7()
-> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6;
    v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
    return v___x_2084_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9()
-> *mut LeanObject {
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8;
    v___x_2087_ = l_Lean_stringToMessageData(v___x_2086_);
    return v___x_2087_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11()
-> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10;
    v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(
    mut v_as_2091_: *mut LeanObject,
    mut v_sz_2092_: usize,
    mut v_i_2093_: usize,
    mut v_b_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v_snd_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_fst_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: usize = 0;
    let mut v___x_2139_: usize = 0;
    let mut v_reuseFailAlloc_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_unused_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2098_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
                if v___x_2098_ == 0 {
                    v___x_2099_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2099_, 0, v_b_2094_);
                    return v___x_2099_;
                } else {
                    v_a_2100_ = lean_array_uget(v_as_2091_, v_i_2093_);
                    v_snd_2101_ = lean_ctor_get(v_a_2100_, 1);
                    v_isSharedCheck_2146_ = (!lean_is_exclusive(v_a_2100_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v_unused_2147_ = lean_ctor_get(v_a_2100_, 0);
                        lean_dec(v_unused_2147_);
                        v___x_2103_ = v_a_2100_;
                        v_isShared_2104_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2101_);
                        lean_dec(v_a_2100_);
                        v___x_2103_ = lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2105_ = lean_ctor_get(v_snd_2101_, 1);
                v_fst_2106_ = lean_ctor_get(v_snd_2101_, 0);
                v_isSharedCheck_2145_ = (!lean_is_exclusive(v_snd_2101_)) as u8;
                if v_isSharedCheck_2145_ == 0 {
                    v___x_2108_ = v_snd_2101_;
                    v_isShared_2109_ = v_isSharedCheck_2145_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2105_);
                    lean_inc(v_fst_2106_);
                    lean_dec(v_snd_2101_);
                    v___x_2108_ = lean_box(0);
                    v_isShared_2109_ = v_isSharedCheck_2145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_2110_ = lean_ctor_get(v_snd_2105_, 0);
                v_snd_2111_ = lean_ctor_get(v_snd_2105_, 1);
                v_isSharedCheck_2144_ = (!lean_is_exclusive(v_snd_2105_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2113_ = v_snd_2105_;
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_2111_);
                    lean_inc(v_fst_2110_);
                    lean_dec(v_snd_2105_);
                    v___x_2113_ = lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2115_ = l_Lean_Linter_linter_constructorNameAsVariable;
                v___x_2116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
                v___x_2117_ = l_Lean_MessageData_ofName(v_fst_2110_);
                lean_inc_ref(v___x_2117_);
                if v_isShared_2114_ == 0 {
                    lean_ctor_set_tag(v___x_2113_, 7);
                    lean_ctor_set(v___x_2113_, 1, v___x_2117_);
                    lean_ctor_set(v___x_2113_, 0, v___x_2116_);
                    v___x_2119_ = v___x_2113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2116_);
                    lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2117_);
                    v___x_2119_ = v_reuseFailAlloc_2143_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2120_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
                if v_isShared_2109_ == 0 {
                    lean_ctor_set_tag(v___x_2108_, 7);
                    lean_ctor_set(v___x_2108_, 1, v___x_2120_);
                    lean_ctor_set(v___x_2108_, 0, v___x_2119_);
                    v___x_2122_ = v___x_2108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2119_);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2123_ = l_Lean_MessageData_ofName(v_snd_2111_);
                lean_inc_ref(v___x_2123_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set_tag(v___x_2103_, 7);
                    lean_ctor_set(v___x_2103_, 1, v___x_2123_);
                    lean_ctor_set(v___x_2103_, 0, v___x_2122_);
                    v___x_2125_ = v___x_2103_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2123_);
                    v___x_2125_ = v_reuseFailAlloc_2141_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2126_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
                v___x_2127_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2127_, 0, v___x_2125_);
                lean_ctor_set(v___x_2127_, 1, v___x_2126_);
                v___x_2128_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
                v___x_2129_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2129_, 0, v___x_2128_);
                lean_ctor_set(v___x_2129_, 1, v___x_2117_);
                v___x_2130_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
                v___x_2131_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2131_, 0, v___x_2129_);
                lean_ctor_set(v___x_2131_, 1, v___x_2130_);
                v___x_2132_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                lean_ctor_set(v___x_2132_, 1, v___x_2123_);
                v___x_2133_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
                v___x_2134_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2134_, 0, v___x_2132_);
                lean_ctor_set(v___x_2134_, 1, v___x_2133_);
                v___x_2135_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2135_, 0, v___x_2127_);
                lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                v___x_2136_ =
                    l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(
                        v___x_2115_,
                        v_fst_2106_,
                        v___x_2135_,
                        v___y_2095_,
                        v___y_2096_,
                    );
                lean_dec(v_fst_2106_);
                if lean_obj_tag(v___x_2136_) == 0 {
                    lean_dec_ref_known(v___x_2136_, 1);
                    v___x_2137_ = lean_box(0);
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
    mut v_as_2148_: *mut LeanObject,
    mut v_sz_2149_: *mut LeanObject,
    mut v_i_2150_: *mut LeanObject,
    mut v_b_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2155_: usize = 0;
    let mut v_i_boxed_2156_: usize = 0;
    let mut v_res_2157_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2149_);
    lean_dec(v_sz_2149_);
    v_i_boxed_2156_ = lean_unbox_usize(v_i_2150_);
    lean_dec(v_i_2150_);
    v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_2148_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2151_, v___y_2152_, v___y_2153_);
    lean_dec(v___y_2153_);
    lean_dec_ref(v___y_2152_);
    lean_dec_ref(v_as_2148_);
    return v_res_2157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(
    mut v___x_2158_: u8,
    mut v_x_2159_: *mut LeanObject,
    mut v_x_2160_: *mut LeanObject,
    mut v_x_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2165_ = lean_box((v___x_2158_) as usize);
    v___x_2166_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(
    mut v___x_2167_: *mut LeanObject,
    mut v_x_2168_: *mut LeanObject,
    mut v_x_2169_: *mut LeanObject,
    mut v_x_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_22304__boxed_2174_: u8 = 0;
    let mut v_res_2175_: *mut LeanObject = core::ptr::null_mut();
    v___x_22304__boxed_2174_ = (lean_unbox(v___x_2167_) as u8);
    v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22304__boxed_2174_, v_x_2168_, v_x_2169_, v_x_2170_, v___y_2171_, v___y_2172_);
    lean_dec(v___y_2172_);
    lean_dec_ref(v___y_2171_);
    lean_dec_ref(v_x_2170_);
    lean_dec_ref(v_x_2169_);
    lean_dec_ref(v_x_2168_);
    return v_res_2175_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(
    mut v_a_2176_: *mut LeanObject,
    mut v_x_2177_: *mut LeanObject,
) -> u8 {
    let mut v___x_2178_: u8 = 0;
    let mut v_key_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2177_) == 0 {
                    v___x_2178_ = 0;
                    return v___x_2178_;
                } else {
                    v_key_2179_ = lean_ctor_get(v_x_2177_, 0);
                    v_tail_2180_ = lean_ctor_get(v_x_2177_, 2);
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
    mut v_a_2183_: *mut LeanObject,
    mut v_x_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_2183_, v_x_2184_);
    lean_dec(v_x_2184_);
    lean_dec_ref(v_a_2183_);
    v_r_2186_ = lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(
    mut v_m_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    v_buckets_2189_ = lean_ctor_get(v_m_2187_, 1);
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
    mut v_m_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2207_: u8 = 0;
    let mut v_r_2208_: *mut LeanObject = core::ptr::null_mut();
    v_res_2207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_2205_, v_a_2206_);
    lean_dec_ref(v_a_2206_);
    lean_dec_ref(v_m_2205_);
    v_r_2208_ = lean_box((v_res_2207_) as usize);
    return v_r_2208_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(
    mut v_a_2209_: *mut LeanObject,
    mut v_b_2210_: *mut LeanObject,
    mut v_x_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2211_) == 0 {
                    lean_dec(v_b_2210_);
                    lean_dec_ref(v_a_2209_);
                    return v_x_2211_;
                } else {
                    v_key_2212_ = lean_ctor_get(v_x_2211_, 0);
                    v_value_2213_ = lean_ctor_get(v_x_2211_, 1);
                    v_tail_2214_ = lean_ctor_get(v_x_2211_, 2);
                    v_isSharedCheck_2226_ = (!lean_is_exclusive(v_x_2211_)) as u8;
                    if v_isSharedCheck_2226_ == 0 {
                        v___x_2216_ = v_x_2211_;
                        v_isShared_2217_ = v_isSharedCheck_2226_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2214_);
                        lean_inc(v_value_2213_);
                        lean_inc(v_key_2212_);
                        lean_dec(v_x_2211_);
                        v___x_2216_ = lean_box(0);
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
                        lean_ctor_set(v___x_2216_, 2, v___x_2219_);
                        v___x_2221_ = v___x_2216_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_key_2212_);
                        lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_value_2213_);
                        lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2219_);
                        v___x_2221_ = v_reuseFailAlloc_2222_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2213_);
                    lean_dec(v_key_2212_);
                    if v_isShared_2217_ == 0 {
                        lean_ctor_set(v___x_2216_, 1, v_b_2210_);
                        lean_ctor_set(v___x_2216_, 0, v_a_2209_);
                        v___x_2224_ = v___x_2216_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2209_);
                        lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_b_2210_);
                        lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_tail_2214_);
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
    mut v_x_2227_: *mut LeanObject,
    mut v_x_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2228_) == 0 {
                    return v_x_2227_;
                } else {
                    v_key_2229_ = lean_ctor_get(v_x_2228_, 0);
                    v_value_2230_ = lean_ctor_get(v_x_2228_, 1);
                    v_tail_2231_ = lean_ctor_get(v_x_2228_, 2);
                    v_isSharedCheck_2254_ = (!lean_is_exclusive(v_x_2228_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2233_ = v_x_2228_;
                        v_isShared_2234_ = v_isSharedCheck_2254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2231_);
                        lean_inc(v_value_2230_);
                        lean_inc(v_key_2229_);
                        lean_dec(v_x_2228_);
                        v___x_2233_ = lean_box(0);
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
                lean_inc(v___x_2248_);
                if v_isShared_2234_ == 0 {
                    lean_ctor_set(v___x_2233_, 2, v___x_2248_);
                    v___x_2250_ = v___x_2233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_key_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_value_2230_);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 2, v___x_2248_);
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
    mut v_i_2255_: *mut LeanObject,
    mut v_source_2256_: *mut LeanObject,
    mut v_target_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: u8 = 0;
    let mut v_es_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_array_get_size(v_source_2256_);
                v___x_2259_ = lean_nat_dec_lt(v_i_2255_, v___x_2258_);
                if v___x_2259_ == 0 {
                    lean_dec_ref(v_source_2256_);
                    lean_dec(v_i_2255_);
                    return v_target_2257_;
                } else {
                    v_es_2260_ = lean_array_fget(v_source_2256_, v_i_2255_);
                    v___x_2261_ = lean_box(0);
                    v_source_2262_ = lean_array_fset(v_source_2256_, v_i_2255_, v___x_2261_);
                    v_target_2263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_2257_, v_es_2260_);
                    v___x_2264_ = lean_unsigned_to_nat(1);
                    v___x_2265_ = lean_nat_add(v_i_2255_, v___x_2264_);
                    lean_dec(v_i_2255_);
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
    mut v_data_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    v___x_2268_ = lean_array_get_size(v_data_2267_);
    v___x_2269_ = lean_unsigned_to_nat(2);
    v_nbuckets_2270_ = lean_nat_mul(v___x_2268_, v___x_2269_);
    v___x_2271_ = lean_unsigned_to_nat(0);
    v___x_2272_ = lean_box(0);
    v___x_2273_ = lean_mk_array(v_nbuckets_2270_, v___x_2272_);
    v___x_2274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_2271_, v_data_2267_, v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(
    mut v_m_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_b_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v_val_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2278_ = lean_ctor_get(v_m_2275_, 0);
                v_buckets_2279_ = lean_ctor_get(v_m_2275_, 1);
                v_isSharedCheck_2322_ = (!lean_is_exclusive(v_m_2275_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v___x_2281_ = v_m_2275_;
                    v_isShared_2282_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2279_);
                    lean_inc(v_size_2278_);
                    lean_dec(v_m_2275_);
                    v___x_2281_ = lean_box(0);
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
                    v___x_2298_ = lean_unsigned_to_nat(1);
                    v_size_x27_2299_ = lean_nat_add(v_size_2278_, v___x_2298_);
                    lean_dec(v_size_2278_);
                    lean_inc(v_bkt_2296_);
                    v___x_2300_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2300_, 0, v_a_2276_);
                    lean_ctor_set(v___x_2300_, 1, v_b_2277_);
                    lean_ctor_set(v___x_2300_, 2, v_bkt_2296_);
                    v_buckets_x27_2301_ =
                        lean_array_uset(v_buckets_2279_, v___x_2295_, v___x_2300_);
                    v___x_2302_ = lean_unsigned_to_nat(4);
                    v___x_2303_ = lean_nat_mul(v_size_x27_2299_, v___x_2302_);
                    v___x_2304_ = lean_unsigned_to_nat(3);
                    v___x_2305_ = lean_nat_div(v___x_2303_, v___x_2304_);
                    lean_dec(v___x_2303_);
                    v___x_2306_ = lean_array_get_size(v_buckets_x27_2301_);
                    v___x_2307_ = lean_nat_dec_le(v___x_2305_, v___x_2306_);
                    lean_dec(v___x_2305_);
                    if v___x_2307_ == 0 {
                        v_val_2308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_2301_);
                        if v_isShared_2282_ == 0 {
                            lean_ctor_set(v___x_2281_, 1, v_val_2308_);
                            lean_ctor_set(v___x_2281_, 0, v_size_x27_2299_);
                            v___x_2310_ = v___x_2281_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_size_x27_2299_);
                            lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_val_2308_);
                            v___x_2310_ = v_reuseFailAlloc_2311_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2282_ == 0 {
                            lean_ctor_set(v___x_2281_, 1, v_buckets_x27_2301_);
                            lean_ctor_set(v___x_2281_, 0, v_size_x27_2299_);
                            v___x_2313_ = v___x_2281_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_size_x27_2299_);
                            lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_buckets_x27_2301_);
                            v___x_2313_ = v_reuseFailAlloc_2314_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2296_);
                    v___x_2315_ = lean_box(0);
                    v_buckets_x27_2316_ =
                        lean_array_uset(v_buckets_2279_, v___x_2295_, v___x_2315_);
                    v___x_2317_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_2276_, v_b_2277_, v_bkt_2296_);
                    v___x_2318_ = lean_array_uset(v_buckets_x27_2316_, v___x_2295_, v___x_2317_);
                    if v_isShared_2282_ == 0 {
                        lean_ctor_set(v___x_2281_, 1, v___x_2318_);
                        v___x_2320_ = v___x_2281_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_size_2278_);
                        lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2318_);
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
    mut v_str_2323_: *mut LeanObject,
    mut v_val_2324_: *mut LeanObject,
    mut v_info_2325_: *mut LeanObject,
    mut v___x_2326_: *mut LeanObject,
    mut v_val_2327_: *mut LeanObject,
    mut v___x_2328_: u8,
    mut v_as_x27_2329_: *mut LeanObject,
    mut v_b_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2329_) == 0 {
                    lean_dec_ref(v_val_2327_);
                    lean_dec(v___x_2326_);
                    v___x_2333_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2333_, 0, v_b_2330_);
                    return v___x_2333_;
                } else {
                    v_head_2334_ = lean_ctor_get(v_as_x27_2329_, 0);
                    v_tail_2335_ = lean_ctor_get(v_as_x27_2329_, 1);
                    v___x_2336_ = lean_st_ref_get(v___y_2331_);
                    v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
                    lean_inc_ref(v_env_2337_);
                    lean_dec(v___x_2336_);
                    v___x_2338_ = lean_box(0);
                    lean_inc(v_head_2334_);
                    v___x_2351_ =
                        l_Lean_Environment_find_x3f(v_env_2337_, v_head_2334_, v___x_2328_);
                    if lean_obj_tag(v___x_2351_) == 1 {
                        v_val_2352_ = lean_ctor_get(v___x_2351_, 0);
                        lean_inc(v_val_2352_);
                        lean_dec_ref_known(v___x_2351_, 1);
                        if lean_obj_tag(v_val_2352_) == 6 {
                            v_val_2353_ = lean_ctor_get(v_val_2352_, 0);
                            lean_inc_ref(v_val_2353_);
                            lean_dec_ref_known(v_val_2352_, 1);
                            v_numFields_2354_ = lean_ctor_get(v_val_2353_, 4);
                            lean_inc(v_numFields_2354_);
                            lean_dec_ref(v_val_2353_);
                            v___x_2355_ = lean_unsigned_to_nat(0);
                            v___x_2356_ = lean_nat_dec_lt(v___x_2355_, v_numFields_2354_);
                            lean_dec(v_numFields_2354_);
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
                            lean_dec(v_val_2352_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2351_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_head_2334_) == 1 {
                    v_str_2340_ = lean_ctor_get(v_head_2334_, 1);
                    v___x_2341_ = lean_string_dec_eq(v_str_2340_, v_str_2323_);
                    if v___x_2341_ == 0 {
                        v_as_x27_2329_ = v_tail_2335_;
                        v_b_2330_ = v___x_2338_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2343_ = lean_st_ref_take(v_val_2324_);
                        v___x_2344_ = l_Lean_Elab_Info_stx(v_info_2325_);
                        lean_inc_ref(v_head_2334_);
                        lean_inc(v___x_2326_);
                        v___x_2345_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2345_, 0, v___x_2326_);
                        lean_ctor_set(v___x_2345_, 1, v_head_2334_);
                        v___x_2346_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2346_, 0, v___x_2344_);
                        lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                        lean_inc_ref(v_val_2327_);
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
    mut v_str_2358_: *mut LeanObject,
    mut v_val_2359_: *mut LeanObject,
    mut v_info_2360_: *mut LeanObject,
    mut v___x_2361_: *mut LeanObject,
    mut v_val_2362_: *mut LeanObject,
    mut v___x_2363_: *mut LeanObject,
    mut v_as_x27_2364_: *mut LeanObject,
    mut v_b_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_22568__boxed_2368_: u8 = 0;
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v___x_22568__boxed_2368_ = (lean_unbox(v___x_2363_) as u8);
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
    lean_dec(v___y_2366_);
    lean_dec(v_as_x27_2364_);
    lean_dec_ref(v_info_2360_);
    lean_dec(v_val_2359_);
    lean_dec_ref(v_str_2358_);
    return v_res_2369_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(
    mut v_ty_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2376_ =
        l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(
            v_ty_2370_,
            v___y_2372_,
        );
    if lean_obj_tag(v___x_2376_) == 0 {
        let mut v_a_2377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
        v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
        lean_inc(v_a_2377_);
        lean_dec_ref_known(v___x_2376_, 1);
        v___x_2378_ = lean_whnf(
            v_a_2377_,
            v___y_2371_,
            v___y_2372_,
            v___y_2373_,
            v___y_2374_,
        );
        return v___x_2378_;
    } else {
        lean_dec(v___y_2374_);
        lean_dec_ref(v___y_2373_);
        lean_dec(v___y_2372_);
        lean_dec_ref(v___y_2371_);
        return v___x_2376_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(
    mut v_ty_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2385_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
    return v_res_2385_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(
    mut v_val_2386_: *mut LeanObject,
    mut v___x_2387_: *mut LeanObject,
    mut v_val_2388_: *mut LeanObject,
    mut v___x_2389_: *mut LeanObject,
    mut v_ci_2390_: *mut LeanObject,
    mut v_info_2391_: *mut LeanObject,
    mut v_x_2392_: *mut LeanObject,
    mut v___y_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isBinder_2400_: u8 = 0;
    let mut v_fvarId_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v_start_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v_toCommandContextInfo_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_unused_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v_a_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v_ref_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_unused_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2506_: u8 = 0;
    let mut v_a_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v_ref_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2523_: u8 = 0;
    let mut v_isSharedCheck_2524_: u8 = 0;
    let mut v_unused_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_a_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut v_unused_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2573_: u8 = 0;
    let mut v_unused_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_2391_) == 1 {
                    v_i_2396_ = lean_ctor_get(v_info_2391_, 0);
                    v_expr_2397_ = lean_ctor_get(v_i_2396_, 3);
                    if lean_obj_tag(v_expr_2397_) == 1 {
                        v_lctx_2398_ = lean_ctor_get(v_i_2396_, 1);
                        v_expectedType_x3f_2399_ = lean_ctor_get(v_i_2396_, 2);
                        v_isBinder_2400_ = lean_ctor_get_uint8(
                            v_i_2396_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        );
                        v_fvarId_2401_ = lean_ctor_get(v_expr_2397_, 0);
                        v___x_2402_ = l_Lean_Elab_Info_range_x3f(v_info_2391_);
                        if lean_obj_tag(v___x_2402_) == 1 {
                            v_val_2403_ = lean_ctor_get(v___x_2402_, 0);
                            v_isSharedCheck_2558_ = (!lean_is_exclusive(v___x_2402_)) as u8;
                            if v_isSharedCheck_2558_ == 0 {
                                v___x_2405_ = v___x_2402_;
                                v_isShared_2406_ = v_isSharedCheck_2558_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_val_2403_);
                                lean_dec(v___x_2402_);
                                v___x_2405_ = lean_box(0);
                                v_isShared_2406_ = v_isSharedCheck_2558_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_2402_);
                            lean_dec_ref(v_ci_2390_);
                            v_isSharedCheck_2565_ = (!lean_is_exclusive(v_info_2391_)) as u8;
                            if v_isSharedCheck_2565_ == 0 {
                                v_unused_2566_ = lean_ctor_get(v_info_2391_, 0);
                                lean_dec(v_unused_2566_);
                                v___x_2560_ = v_info_2391_;
                                v_isShared_2561_ = v_isSharedCheck_2565_;
                                state = 33;
                                continue;
                            } else {
                                lean_dec(v_info_2391_);
                                v___x_2560_ = lean_box(0);
                                v_isShared_2561_ = v_isSharedCheck_2565_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_ci_2390_);
                        v_isSharedCheck_2573_ = (!lean_is_exclusive(v_info_2391_)) as u8;
                        if v_isSharedCheck_2573_ == 0 {
                            v_unused_2574_ = lean_ctor_get(v_info_2391_, 0);
                            lean_dec(v_unused_2574_);
                            v___x_2568_ = v_info_2391_;
                            v_isShared_2569_ = v_isSharedCheck_2573_;
                            state = 35;
                            continue;
                        } else {
                            lean_dec(v_info_2391_);
                            v___x_2568_ = lean_box(0);
                            v_isShared_2569_ = v_isSharedCheck_2573_;
                            state = 35;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_info_2391_);
                    lean_dec_ref(v_ci_2390_);
                    v___x_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2575_, 0, v___x_2387_);
                    return v___x_2575_;
                }
            }
            1 => {
                v___x_2407_ = lean_st_ref_get(v_val_2386_);
                v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_2407_, v_val_2403_);
                lean_dec(v___x_2407_);
                if v___x_2408_ == 0 {
                    v___x_2409_ = l_Lean_Elab_Info_stx(v_info_2391_);
                    v___x_2410_ = l_Lean_Syntax_getHeadInfo(v___x_2409_);
                    if lean_obj_tag(v___x_2410_) == 0 {
                        lean_dec_ref_known(v___x_2410_, 4);
                        if v_isBinder_2400_ == 0 {
                            lean_dec(v___x_2409_);
                            lean_dec(v_val_2403_);
                            lean_dec_ref_known(v_info_2391_, 1);
                            lean_dec_ref(v_ci_2390_);
                            if v_isShared_2406_ == 0 {
                                lean_ctor_set_tag(v___x_2405_, 0);
                                lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                                v___x_2412_ = v___x_2405_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2387_);
                                v___x_2412_ = v_reuseFailAlloc_2413_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc(v_fvarId_2401_);
                            lean_inc_ref(v_lctx_2398_);
                            v___x_2414_ = lean_local_ctx_find(v_lctx_2398_, v_fvarId_2401_);
                            if lean_obj_tag(v___x_2414_) == 1 {
                                v_val_2415_ = lean_ctor_get(v___x_2414_, 0);
                                v_isSharedCheck_2548_ = (!lean_is_exclusive(v___x_2414_)) as u8;
                                if v_isSharedCheck_2548_ == 0 {
                                    v___x_2417_ = v___x_2414_;
                                    v_isShared_2418_ = v_isSharedCheck_2548_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_val_2415_);
                                    lean_dec(v___x_2414_);
                                    v___x_2417_ = lean_box(0);
                                    v_isShared_2418_ = v_isSharedCheck_2548_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2414_);
                                lean_dec(v___x_2409_);
                                lean_dec(v_val_2403_);
                                lean_dec_ref_known(v_info_2391_, 1);
                                lean_dec_ref(v_ci_2390_);
                                if v_isShared_2406_ == 0 {
                                    lean_ctor_set_tag(v___x_2405_, 0);
                                    lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                                    v___x_2550_ = v___x_2405_;
                                    state = 30;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2387_);
                                    v___x_2550_ = v_reuseFailAlloc_2551_;
                                    state = 30;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v___x_2410_);
                        lean_dec(v___x_2409_);
                        lean_dec(v_val_2403_);
                        lean_dec_ref_known(v_info_2391_, 1);
                        lean_dec_ref(v_ci_2390_);
                        if v_isShared_2406_ == 0 {
                            lean_ctor_set_tag(v___x_2405_, 0);
                            lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                            v___x_2553_ = v___x_2405_;
                            state = 31;
                            continue;
                        } else {
                            v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2387_);
                            v___x_2553_ = v_reuseFailAlloc_2554_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_2403_);
                    lean_dec_ref_known(v_info_2391_, 1);
                    lean_dec_ref(v_ci_2390_);
                    if v_isShared_2406_ == 0 {
                        lean_ctor_set_tag(v___x_2405_, 0);
                        lean_ctor_set(v___x_2405_, 0, v___x_2387_);
                        v___x_2556_ = v___x_2405_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2387_);
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
                v_start_2419_ = lean_ctor_get(v_val_2403_, 0);
                v___x_2420_ = l_Lean_Syntax_Range_contains(v_val_2388_, v_start_2419_, v___x_2408_);
                if v___x_2420_ == 0 {
                    lean_dec(v_val_2415_);
                    lean_dec(v___x_2409_);
                    lean_del_object(v___x_2405_);
                    lean_dec(v_val_2403_);
                    lean_dec_ref_known(v_info_2391_, 1);
                    lean_dec_ref(v_ci_2390_);
                    if v_isShared_2418_ == 0 {
                        lean_ctor_set_tag(v___x_2417_, 0);
                        lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                        v___x_2422_ = v___x_2417_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2387_);
                        v___x_2422_ = v_reuseFailAlloc_2423_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v___x_2408_ == 0 {
                        v___x_2424_ = l_Lean_LocalDecl_userName(v_val_2415_);
                        lean_dec(v_val_2415_);
                        v___x_2425_ = l_Lean_Name_hasMacroScopes(v___x_2424_);
                        lean_dec(v___x_2424_);
                        if v___x_2425_ == 0 {
                            v_toCommandContextInfo_2426_ = lean_ctor_get(v_ci_2390_, 0);
                            v_options_2427_ = lean_ctor_get(v_toCommandContextInfo_2426_, 4);
                            lean_inc_ref(v_options_2427_);
                            v___x_2428_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_2427_, v___y_2394_);
                            if lean_obj_tag(v___x_2428_) == 0 {
                                v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
                                v_isSharedCheck_2533_ = (!lean_is_exclusive(v___x_2428_)) as u8;
                                if v_isSharedCheck_2533_ == 0 {
                                    v___x_2431_ = v___x_2428_;
                                    v_isShared_2432_ = v_isSharedCheck_2533_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2429_);
                                    lean_dec(v___x_2428_);
                                    v___x_2431_ = lean_box(0);
                                    v_isShared_2432_ = v_isSharedCheck_2533_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_2417_);
                                lean_dec(v___x_2409_);
                                lean_del_object(v___x_2405_);
                                lean_dec(v_val_2403_);
                                lean_dec_ref_known(v_info_2391_, 1);
                                lean_dec_ref(v_ci_2390_);
                                v_a_2534_ = lean_ctor_get(v___x_2428_, 0);
                                v_isSharedCheck_2541_ = (!lean_is_exclusive(v___x_2428_)) as u8;
                                if v_isSharedCheck_2541_ == 0 {
                                    v___x_2536_ = v___x_2428_;
                                    v_isShared_2537_ = v_isSharedCheck_2541_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_2534_);
                                    lean_dec(v___x_2428_);
                                    v___x_2536_ = lean_box(0);
                                    v_isShared_2537_ = v_isSharedCheck_2541_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2409_);
                            lean_del_object(v___x_2405_);
                            lean_dec(v_val_2403_);
                            lean_dec_ref_known(v_info_2391_, 1);
                            lean_dec_ref(v_ci_2390_);
                            if v_isShared_2418_ == 0 {
                                lean_ctor_set_tag(v___x_2417_, 0);
                                lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                                v___x_2543_ = v___x_2417_;
                                state = 28;
                                continue;
                            } else {
                                v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2387_);
                                v___x_2543_ = v_reuseFailAlloc_2544_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_2415_);
                        lean_dec(v___x_2409_);
                        lean_del_object(v___x_2405_);
                        lean_dec(v_val_2403_);
                        lean_dec_ref_known(v_info_2391_, 1);
                        lean_dec_ref(v_ci_2390_);
                        if v_isShared_2418_ == 0 {
                            lean_ctor_set_tag(v___x_2417_, 0);
                            lean_ctor_set(v___x_2417_, 0, v___x_2387_);
                            v___x_2546_ = v___x_2417_;
                            state = 29;
                            continue;
                        } else {
                            v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2387_);
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
                lean_dec(v_a_2429_);
                if v___x_2433_ == 0 {
                    lean_del_object(v___x_2417_);
                    lean_dec(v___x_2409_);
                    lean_del_object(v___x_2405_);
                    lean_dec(v_val_2403_);
                    lean_dec_ref_known(v_info_2391_, 1);
                    lean_dec_ref(v_ci_2390_);
                    if v_isShared_2432_ == 0 {
                        lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                        v___x_2435_ = v___x_2431_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2387_);
                        v___x_2435_ = v_reuseFailAlloc_2436_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2437_ = l_Lean_Syntax_getId(v___x_2409_);
                    lean_dec(v___x_2409_);
                    if lean_obj_tag(v___x_2437_) == 1 {
                        v_pre_2438_ = lean_ctor_get(v___x_2437_, 0);
                        lean_inc(v_pre_2438_);
                        v_str_2439_ = lean_ctor_get(v___x_2437_, 1);
                        lean_inc_ref(v_str_2439_);
                        if lean_obj_tag(v_pre_2438_) == 0 {
                            lean_del_object(v___x_2431_);
                            if lean_obj_tag(v_expectedType_x3f_2399_) == 1 {
                                lean_del_object(v___x_2405_);
                                v_val_2500_ = lean_ctor_get(v_expectedType_x3f_2399_, 0);
                                lean_inc(v_val_2500_);
                                v_ty_2441_ = v_val_2500_;
                                v___y_2442_ = v___y_2393_;
                                v___y_2443_ = v___y_2394_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc_ref(v_expr_2397_);
                                v___x_2501_ = lean_alloc_closure(
                                    l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                                    6,
                                    1,
                                );
                                lean_closure_set(v___x_2501_, 0, v_expr_2397_);
                                lean_inc_ref(v_ci_2390_);
                                lean_inc_ref(v_i_2396_);
                                v___x_2502_ = l_Lean_Elab_TermInfo_runMetaM___redArg(
                                    v_i_2396_,
                                    v_ci_2390_,
                                    v___x_2501_,
                                );
                                if lean_obj_tag(v___x_2502_) == 0 {
                                    lean_del_object(v___x_2405_);
                                    v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
                                    lean_inc(v_a_2503_);
                                    lean_dec_ref_known(v___x_2502_, 1);
                                    v_ty_2441_ = v_a_2503_;
                                    v___y_2442_ = v___y_2393_;
                                    v___y_2443_ = v___y_2394_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec_ref(v_str_2439_);
                                    lean_dec_ref_known(v___x_2437_, 2);
                                    lean_del_object(v___x_2417_);
                                    lean_dec_ref_known(v_info_2391_, 1);
                                    lean_dec_ref(v_ci_2390_);
                                    v_isSharedCheck_2524_ = (!lean_is_exclusive(v_val_2403_)) as u8;
                                    if v_isSharedCheck_2524_ == 0 {
                                        v_unused_2525_ = lean_ctor_get(v_val_2403_, 1);
                                        lean_dec(v_unused_2525_);
                                        v_unused_2526_ = lean_ctor_get(v_val_2403_, 0);
                                        lean_dec(v_unused_2526_);
                                        v___x_2505_ = v_val_2403_;
                                        v_isShared_2506_ = v_isSharedCheck_2524_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_dec(v_val_2403_);
                                        v___x_2505_ = lean_box(0);
                                        v_isShared_2506_ = v_isSharedCheck_2524_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_str_2439_);
                            lean_dec(v_pre_2438_);
                            lean_dec_ref_known(v___x_2437_, 2);
                            lean_del_object(v___x_2417_);
                            lean_del_object(v___x_2405_);
                            lean_dec(v_val_2403_);
                            lean_dec_ref_known(v_info_2391_, 1);
                            lean_dec_ref(v_ci_2390_);
                            if v_isShared_2432_ == 0 {
                                lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                                v___x_2528_ = v___x_2431_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2387_);
                                v___x_2528_ = v_reuseFailAlloc_2529_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2437_);
                        lean_del_object(v___x_2417_);
                        lean_del_object(v___x_2405_);
                        lean_dec(v_val_2403_);
                        lean_dec_ref_known(v_info_2391_, 1);
                        lean_dec_ref(v_ci_2390_);
                        if v_isShared_2432_ == 0 {
                            lean_ctor_set(v___x_2431_, 0, v___x_2387_);
                            v___x_2531_ = v___x_2431_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2387_);
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
                v___f_2444_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed as *mut core::ffi::c_void, 6, 1);
                lean_closure_set(v___f_2444_, 0, v_ty_2441_);
                lean_inc_ref(v_i_2396_);
                v___x_2445_ =
                    l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_2396_, v_ci_2390_, v___f_2444_);
                if lean_obj_tag(v___x_2445_) == 0 {
                    lean_del_object(v___x_2417_);
                    v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2476_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2448_ = v___x_2445_;
                        v_isShared_2449_ = v_isSharedCheck_2476_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2446_);
                        lean_dec(v___x_2445_);
                        v___x_2448_ = lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2476_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_str_2439_);
                    lean_dec_ref_known(v___x_2437_, 2);
                    lean_dec_ref_known(v_info_2391_, 1);
                    v_isSharedCheck_2497_ = (!lean_is_exclusive(v_val_2403_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v_unused_2498_ = lean_ctor_get(v_val_2403_, 1);
                        lean_dec(v_unused_2498_);
                        v_unused_2499_ = lean_ctor_get(v_val_2403_, 0);
                        lean_dec(v_unused_2499_);
                        v___x_2478_ = v_val_2403_;
                        v_isShared_2479_ = v_isSharedCheck_2497_;
                        state = 14;
                        continue;
                    } else {
                        lean_dec(v_val_2403_);
                        v___x_2478_ = lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2497_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2450_ = l_Lean_Expr_getAppFn_x27(v_a_2446_);
                lean_dec(v_a_2446_);
                if lean_obj_tag(v___x_2450_) == 4 {
                    v_declName_2451_ = lean_ctor_get(v___x_2450_, 0);
                    lean_inc(v_declName_2451_);
                    lean_dec_ref_known(v___x_2450_, 2);
                    v___x_2452_ = lean_st_ref_get(v___y_2443_);
                    v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
                    lean_inc_ref(v_env_2453_);
                    lean_dec(v___x_2452_);
                    v___x_2454_ =
                        l_Lean_Environment_find_x3f(v_env_2453_, v_declName_2451_, v___x_2408_);
                    if lean_obj_tag(v___x_2454_) == 1 {
                        v_val_2455_ = lean_ctor_get(v___x_2454_, 0);
                        lean_inc(v_val_2455_);
                        lean_dec_ref_known(v___x_2454_, 1);
                        if lean_obj_tag(v_val_2455_) == 5 {
                            lean_del_object(v___x_2448_);
                            v_val_2456_ = lean_ctor_get(v_val_2455_, 0);
                            lean_inc_ref(v_val_2456_);
                            lean_dec_ref_known(v_val_2455_, 1);
                            v_ctors_2457_ = lean_ctor_get(v_val_2456_, 4);
                            lean_inc(v_ctors_2457_);
                            lean_dec_ref(v_val_2456_);
                            v___x_2458_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_2439_, v_val_2386_, v_info_2391_, v___x_2437_, v_val_2403_, v___x_2408_, v_ctors_2457_, v___x_2387_, v___y_2443_);
                            lean_dec(v_ctors_2457_);
                            lean_dec_ref_known(v_info_2391_, 1);
                            lean_dec_ref(v_str_2439_);
                            if lean_obj_tag(v___x_2458_) == 0 {
                                v_isSharedCheck_2465_ = (!lean_is_exclusive(v___x_2458_)) as u8;
                                if v_isSharedCheck_2465_ == 0 {
                                    v_unused_2466_ = lean_ctor_get(v___x_2458_, 0);
                                    lean_dec(v_unused_2466_);
                                    v___x_2460_ = v___x_2458_;
                                    v_isShared_2461_ = v_isSharedCheck_2465_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec(v___x_2458_);
                                    v___x_2460_ = lean_box(0);
                                    v_isShared_2461_ = v_isSharedCheck_2465_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                return v___x_2458_;
                            }
                        } else {
                            lean_dec(v_val_2455_);
                            lean_dec_ref(v_str_2439_);
                            lean_dec_ref_known(v___x_2437_, 2);
                            lean_dec(v_val_2403_);
                            lean_dec_ref_known(v_info_2391_, 1);
                            if v_isShared_2449_ == 0 {
                                lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                                v___x_2468_ = v___x_2448_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2387_);
                                v___x_2468_ = v_reuseFailAlloc_2469_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2454_);
                        lean_dec_ref(v_str_2439_);
                        lean_dec_ref_known(v___x_2437_, 2);
                        lean_dec(v_val_2403_);
                        lean_dec_ref_known(v_info_2391_, 1);
                        if v_isShared_2449_ == 0 {
                            lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                            v___x_2471_ = v___x_2448_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2387_);
                            v___x_2471_ = v_reuseFailAlloc_2472_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2450_);
                    lean_dec_ref(v_str_2439_);
                    lean_dec_ref_known(v___x_2437_, 2);
                    lean_dec(v_val_2403_);
                    lean_dec_ref_known(v_info_2391_, 1);
                    if v_isShared_2449_ == 0 {
                        lean_ctor_set(v___x_2448_, 0, v___x_2387_);
                        v___x_2474_ = v___x_2448_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2387_);
                        v___x_2474_ = v_reuseFailAlloc_2475_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2461_ == 0 {
                    lean_ctor_set(v___x_2460_, 0, v___x_2387_);
                    v___x_2463_ = v___x_2460_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2387_);
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
                v_a_2480_ = lean_ctor_get(v___x_2445_, 0);
                v_isSharedCheck_2496_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                if v_isSharedCheck_2496_ == 0 {
                    v___x_2482_ = v___x_2445_;
                    v_isShared_2483_ = v_isSharedCheck_2496_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_a_2480_);
                    lean_dec(v___x_2445_);
                    v___x_2482_ = lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2496_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_ref_2484_ = lean_ctor_get(v___y_2442_, 7);
                v___x_2485_ = lean_io_error_to_string(v_a_2480_);
                if v_isShared_2418_ == 0 {
                    lean_ctor_set_tag(v___x_2417_, 3);
                    lean_ctor_set(v___x_2417_, 0, v___x_2485_);
                    v___x_2487_ = v___x_2417_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2485_);
                    v___x_2487_ = v_reuseFailAlloc_2495_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2488_ = l_Lean_MessageData_ofFormat(v___x_2487_);
                lean_inc(v_ref_2484_);
                if v_isShared_2479_ == 0 {
                    lean_ctor_set(v___x_2478_, 1, v___x_2488_);
                    lean_ctor_set(v___x_2478_, 0, v_ref_2484_);
                    v___x_2490_ = v___x_2478_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_ref_2484_);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2488_);
                    v___x_2490_ = v_reuseFailAlloc_2494_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2483_ == 0 {
                    lean_ctor_set(v___x_2482_, 0, v___x_2490_);
                    v___x_2492_ = v___x_2482_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                    v___x_2492_ = v_reuseFailAlloc_2493_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2492_;
            }
            19 => {
                v_a_2507_ = lean_ctor_get(v___x_2502_, 0);
                v_isSharedCheck_2523_ = (!lean_is_exclusive(v___x_2502_)) as u8;
                if v_isSharedCheck_2523_ == 0 {
                    v___x_2509_ = v___x_2502_;
                    v_isShared_2510_ = v_isSharedCheck_2523_;
                    state = 20;
                    continue;
                } else {
                    lean_inc(v_a_2507_);
                    lean_dec(v___x_2502_);
                    v___x_2509_ = lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2523_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_ref_2511_ = lean_ctor_get(v___y_2393_, 7);
                v___x_2512_ = lean_io_error_to_string(v_a_2507_);
                if v_isShared_2406_ == 0 {
                    lean_ctor_set_tag(v___x_2405_, 3);
                    lean_ctor_set(v___x_2405_, 0, v___x_2512_);
                    v___x_2514_ = v___x_2405_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2522_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
                    v___x_2514_ = v_reuseFailAlloc_2522_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2515_ = l_Lean_MessageData_ofFormat(v___x_2514_);
                lean_inc(v_ref_2511_);
                if v_isShared_2506_ == 0 {
                    lean_ctor_set(v___x_2505_, 1, v___x_2515_);
                    lean_ctor_set(v___x_2505_, 0, v_ref_2511_);
                    v___x_2517_ = v___x_2505_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_ref_2511_);
                    lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2515_);
                    v___x_2517_ = v_reuseFailAlloc_2521_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2510_ == 0 {
                    lean_ctor_set(v___x_2509_, 0, v___x_2517_);
                    v___x_2519_ = v___x_2509_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
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
                    v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
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
                    lean_ctor_set_tag(v___x_2560_, 0);
                    lean_ctor_set(v___x_2560_, 0, v___x_2387_);
                    v___x_2563_ = v___x_2560_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2387_);
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
                    lean_ctor_set_tag(v___x_2568_, 0);
                    lean_ctor_set(v___x_2568_, 0, v___x_2387_);
                    v___x_2571_ = v___x_2568_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2387_);
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
    mut v_val_2576_: *mut LeanObject,
    mut v___x_2577_: *mut LeanObject,
    mut v_val_2578_: *mut LeanObject,
    mut v___x_2579_: *mut LeanObject,
    mut v_ci_2580_: *mut LeanObject,
    mut v_info_2581_: *mut LeanObject,
    mut v_x_2582_: *mut LeanObject,
    mut v___y_2583_: *mut LeanObject,
    mut v___y_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2586_: *mut LeanObject = core::ptr::null_mut();
    v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_2576_, v___x_2577_, v_val_2578_, v___x_2579_, v_ci_2580_, v_info_2581_, v_x_2582_, v___y_2583_, v___y_2584_);
    lean_dec(v___y_2584_);
    lean_dec_ref(v___y_2583_);
    lean_dec_ref(v_x_2582_);
    lean_dec_ref(v___x_2579_);
    lean_dec_ref(v_val_2578_);
    lean_dec(v_val_2576_);
    return v_res_2586_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(
    mut v_postNode_2587_: *mut LeanObject,
    mut v_ci_2588_: *mut LeanObject,
    mut v_i_2589_: *mut LeanObject,
    mut v_cs_2590_: *mut LeanObject,
    mut v_x_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2593_);
    lean_inc_ref(v___y_2592_);
    v___x_2595_ = lean_apply_6(
        v_postNode_2587_,
        v_ci_2588_,
        v_i_2589_,
        v_cs_2590_,
        v___y_2592_,
        v___y_2593_,
        lean_box(0),
    );
    return v___x_2595_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(
    mut v_postNode_2596_: *mut LeanObject,
    mut v_ci_2597_: *mut LeanObject,
    mut v_i_2598_: *mut LeanObject,
    mut v_cs_2599_: *mut LeanObject,
    mut v_x_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2604_: *mut LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_2596_, v_ci_2597_, v_i_2598_, v_cs_2599_, v_x_2600_, v___y_2601_, v___y_2602_);
    lean_dec(v___y_2602_);
    lean_dec_ref(v___y_2601_);
    lean_dec(v_x_2600_);
    return v_res_2604_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    v___x_2605_ = l_instMonadEIO(lean_box(0));
    return v___x_2605_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(
    mut v_msg_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v_toFunctor_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___f_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_18811__overap_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_unused_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_unused_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2612_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
                v___x_2613_ = l_StateRefT_x27_instMonad___redArg(v___x_2612_);
                v_toApplicative_2614_ = lean_ctor_get(v___x_2613_, 0);
                v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2613_)) as u8;
                if v_isSharedCheck_2645_ == 0 {
                    v_unused_2646_ = lean_ctor_get(v___x_2613_, 1);
                    lean_dec(v_unused_2646_);
                    v___x_2616_ = v___x_2613_;
                    v_isShared_2617_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2614_);
                    lean_dec(v___x_2613_);
                    v___x_2616_ = lean_box(0);
                    v_isShared_2617_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2618_ = lean_ctor_get(v_toApplicative_2614_, 0);
                v_toSeq_2619_ = lean_ctor_get(v_toApplicative_2614_, 2);
                v_toSeqLeft_2620_ = lean_ctor_get(v_toApplicative_2614_, 3);
                v_toSeqRight_2621_ = lean_ctor_get(v_toApplicative_2614_, 4);
                v_isSharedCheck_2643_ = (!lean_is_exclusive(v_toApplicative_2614_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v_unused_2644_ = lean_ctor_get(v_toApplicative_2614_, 1);
                    lean_dec(v_unused_2644_);
                    v___x_2623_ = v_toApplicative_2614_;
                    v_isShared_2624_ = v_isSharedCheck_2643_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2621_);
                    lean_inc(v_toSeqLeft_2620_);
                    lean_inc(v_toSeq_2619_);
                    lean_inc(v_toFunctor_2618_);
                    lean_dec(v_toApplicative_2614_);
                    v___x_2623_ = lean_box(0);
                    v_isShared_2624_ = v_isSharedCheck_2643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2625_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1;
                v___f_2626_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2;
                lean_inc_ref(v_toFunctor_2618_);
                v___f_2627_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2627_, 0, v_toFunctor_2618_);
                v___f_2628_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2628_, 0, v_toFunctor_2618_);
                v___x_2629_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2629_, 0, v___f_2627_);
                lean_ctor_set(v___x_2629_, 1, v___f_2628_);
                v___f_2630_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2630_, 0, v_toSeqRight_2621_);
                v___f_2631_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2631_, 0, v_toSeqLeft_2620_);
                v___f_2632_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2632_, 0, v_toSeq_2619_);
                if v_isShared_2624_ == 0 {
                    lean_ctor_set(v___x_2623_, 4, v___f_2630_);
                    lean_ctor_set(v___x_2623_, 3, v___f_2631_);
                    lean_ctor_set(v___x_2623_, 2, v___f_2632_);
                    lean_ctor_set(v___x_2623_, 1, v___f_2625_);
                    lean_ctor_set(v___x_2623_, 0, v___x_2629_);
                    v___x_2634_ = v___x_2623_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2629_);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___f_2625_);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 2, v___f_2632_);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 3, v___f_2631_);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___f_2630_);
                    v___x_2634_ = v_reuseFailAlloc_2642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2617_ == 0 {
                    lean_ctor_set(v___x_2616_, 1, v___f_2626_);
                    lean_ctor_set(v___x_2616_, 0, v___x_2634_);
                    v___x_2636_ = v___x_2616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2634_);
                    lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___f_2626_);
                    v___x_2636_ = v_reuseFailAlloc_2641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2637_ = lean_box(0);
                v___x_2638_ = l_instInhabitedOfMonad___redArg(v___x_2636_, v___x_2637_);
                v___x_18811__overap_2639_ = lean_panic_fn_borrowed(v___x_2638_, v_msg_2608_);
                lean_dec(v___x_2638_);
                lean_inc(v___y_2610_);
                lean_inc_ref(v___y_2609_);
                v___x_2640_ = lean_apply_3(
                    v___x_18811__overap_2639_,
                    v___y_2609_,
                    v___y_2610_,
                    lean_box(0),
                );
                return v___x_2640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(
    mut v_msg_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2651_: *mut LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_2647_, v___y_2648_, v___y_2649_);
    lean_dec(v___y_2649_);
    lean_dec_ref(v___y_2648_);
    return v_res_2651_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2;
    v___x_2656_ = lean_unsigned_to_nat(21);
    v___x_2657_ = lean_unsigned_to_nat(65);
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
    mut v_preNode_2661_: *mut LeanObject,
    mut v_postNode_2662_: *mut LeanObject,
    mut v_x_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_unused_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_a_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_a_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2740_: u8 = 0;
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut v_unused_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2664_) {
                0 => {
                    v_i_2668_ = lean_ctor_get(v_x_2664_, 0);
                    lean_inc_ref(v_i_2668_);
                    v_t_2669_ = lean_ctor_get(v_x_2664_, 1);
                    lean_inc_ref(v_t_2669_);
                    lean_dec_ref_known(v_x_2664_, 2);
                    v___x_2670_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2668_, v_x_2663_);
                    v_x_2663_ = v___x_2670_;
                    v_x_2664_ = v_t_2669_;
                    state = 0;
                    continue;
                }
                1 => {
                    if lean_obj_tag(v_x_2663_) == 0 {
                        lean_dec_ref_known(v_x_2664_, 2);
                        lean_dec_ref(v_postNode_2662_);
                        lean_dec_ref(v_preNode_2661_);
                        v___x_2672_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
                        v___x_2673_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_2672_, v___y_2665_, v___y_2666_);
                        return v___x_2673_;
                    } else {
                        v_i_2674_ = lean_ctor_get(v_x_2664_, 0);
                        lean_inc_ref_n(v_i_2674_, 2);
                        v_children_2675_ = lean_ctor_get(v_x_2664_, 1);
                        lean_inc_ref_n(v_children_2675_, 2);
                        lean_dec_ref_known(v_x_2664_, 2);
                        v_val_2676_ = lean_ctor_get(v_x_2663_, 0);
                        lean_inc_n(v_val_2676_, 2);
                        lean_inc_ref(v_preNode_2661_);
                        lean_inc(v___y_2666_);
                        lean_inc_ref(v___y_2665_);
                        v___x_2677_ = lean_apply_6(
                            v_preNode_2661_,
                            v_val_2676_,
                            v_i_2674_,
                            v_children_2675_,
                            v___y_2665_,
                            v___y_2666_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_2677_) == 0 {
                            v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
                            lean_inc(v_a_2678_);
                            lean_dec_ref_known(v___x_2677_, 1);
                            v___x_2679_ = (lean_unbox(v_a_2678_) as u8);
                            lean_dec(v_a_2678_);
                            if v___x_2679_ == 0 {
                                lean_dec_ref(v_preNode_2661_);
                                v_isSharedCheck_2704_ = (!lean_is_exclusive(v_x_2663_)) as u8;
                                if v_isSharedCheck_2704_ == 0 {
                                    v_unused_2705_ = lean_ctor_get(v_x_2663_, 0);
                                    lean_dec(v_unused_2705_);
                                    v___x_2681_ = v_x_2663_;
                                    v_isShared_2682_ = v_isSharedCheck_2704_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_x_2663_);
                                    v___x_2681_ = lean_box(0);
                                    v_isShared_2682_ = v_isSharedCheck_2704_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2706_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_2663_, v_i_2674_);
                                v___x_2707_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_2675_);
                                v___x_2708_ = lean_box(0);
                                lean_inc_ref(v_postNode_2662_);
                                v___x_2709_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_2661_, v_postNode_2662_, v___x_2706_, v___x_2707_, v___x_2708_, v___y_2665_, v___y_2666_);
                                if lean_obj_tag(v___x_2709_) == 0 {
                                    v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
                                    lean_inc(v_a_2710_);
                                    lean_dec_ref_known(v___x_2709_, 1);
                                    lean_inc(v___y_2666_);
                                    lean_inc_ref(v___y_2665_);
                                    v___x_2711_ = lean_apply_7(
                                        v_postNode_2662_,
                                        v_val_2676_,
                                        v_i_2674_,
                                        v_children_2675_,
                                        v_a_2710_,
                                        v___y_2665_,
                                        v___y_2666_,
                                        lean_box(0),
                                    );
                                    if lean_obj_tag(v___x_2711_) == 0 {
                                        v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
                                        v_isSharedCheck_2720_ =
                                            (!lean_is_exclusive(v___x_2711_)) as u8;
                                        if v_isSharedCheck_2720_ == 0 {
                                            v___x_2714_ = v___x_2711_;
                                            v_isShared_2715_ = v_isSharedCheck_2720_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2712_);
                                            lean_dec(v___x_2711_);
                                            v___x_2714_ = lean_box(0);
                                            v_isShared_2715_ = v_isSharedCheck_2720_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_2721_ = lean_ctor_get(v___x_2711_, 0);
                                        v_isSharedCheck_2728_ =
                                            (!lean_is_exclusive(v___x_2711_)) as u8;
                                        if v_isSharedCheck_2728_ == 0 {
                                            v___x_2723_ = v___x_2711_;
                                            v_isShared_2724_ = v_isSharedCheck_2728_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2721_);
                                            lean_dec(v___x_2711_);
                                            v___x_2723_ = lean_box(0);
                                            v_isShared_2724_ = v_isSharedCheck_2728_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_2676_);
                                    lean_dec_ref(v_children_2675_);
                                    lean_dec_ref(v_i_2674_);
                                    lean_dec_ref(v_postNode_2662_);
                                    v_a_2729_ = lean_ctor_get(v___x_2709_, 0);
                                    v_isSharedCheck_2736_ = (!lean_is_exclusive(v___x_2709_)) as u8;
                                    if v_isSharedCheck_2736_ == 0 {
                                        v___x_2731_ = v___x_2709_;
                                        v_isShared_2732_ = v_isSharedCheck_2736_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2729_);
                                        lean_dec(v___x_2709_);
                                        v___x_2731_ = lean_box(0);
                                        v_isShared_2732_ = v_isSharedCheck_2736_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_val_2676_);
                            lean_dec_ref(v_children_2675_);
                            lean_dec_ref_known(v_x_2663_, 1);
                            lean_dec_ref(v_i_2674_);
                            lean_dec_ref(v_postNode_2662_);
                            lean_dec_ref(v_preNode_2661_);
                            v_a_2737_ = lean_ctor_get(v___x_2677_, 0);
                            v_isSharedCheck_2744_ = (!lean_is_exclusive(v___x_2677_)) as u8;
                            if v_isSharedCheck_2744_ == 0 {
                                v___x_2739_ = v___x_2677_;
                                v_isShared_2740_ = v_isSharedCheck_2744_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_2737_);
                                lean_dec(v___x_2677_);
                                v___x_2739_ = lean_box(0);
                                v_isShared_2740_ = v_isSharedCheck_2744_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    lean_dec(v_x_2663_);
                    lean_dec_ref(v_postNode_2662_);
                    lean_dec_ref(v_preNode_2661_);
                    v_isSharedCheck_2752_ = (!lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v_unused_2753_ = lean_ctor_get(v_x_2664_, 0);
                        lean_dec(v_unused_2753_);
                        v___x_2746_ = v_x_2664_;
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 15;
                        continue;
                    } else {
                        lean_dec(v_x_2664_);
                        v___x_2746_ = lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2683_ = lean_box(0);
                lean_inc(v___y_2666_);
                lean_inc_ref(v___y_2665_);
                v___x_2684_ = lean_apply_7(
                    v_postNode_2662_,
                    v_val_2676_,
                    v_i_2674_,
                    v_children_2675_,
                    v___x_2683_,
                    v___y_2665_,
                    v___y_2666_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2684_) == 0 {
                    v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2695_ = (!lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2695_ == 0 {
                        v___x_2687_ = v___x_2684_;
                        v_isShared_2688_ = v_isSharedCheck_2695_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2685_);
                        lean_dec(v___x_2684_);
                        v___x_2687_ = lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2695_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2681_);
                    v_a_2696_ = lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2703_ = (!lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2698_ = v___x_2684_;
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2696_);
                        lean_dec(v___x_2684_);
                        v___x_2698_ = lean_box(0);
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2682_ == 0 {
                    lean_ctor_set(v___x_2681_, 0, v_a_2685_);
                    v___x_2690_ = v___x_2681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2685_);
                    v___x_2690_ = v_reuseFailAlloc_2694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2688_ == 0 {
                    lean_ctor_set(v___x_2687_, 0, v___x_2690_);
                    v___x_2692_ = v___x_2687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
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
                    v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2701_;
            }
            7 => {
                v___x_2716_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2716_, 0, v_a_2712_);
                if v_isShared_2715_ == 0 {
                    lean_ctor_set(v___x_2714_, 0, v___x_2716_);
                    v___x_2718_ = v___x_2714_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
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
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
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
                    v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
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
                    v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
                    v___x_2742_ = v_reuseFailAlloc_2743_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2742_;
            }
            15 => {
                v___x_2748_ = lean_box(0);
                if v_isShared_2747_ == 0 {
                    lean_ctor_set_tag(v___x_2746_, 0);
                    lean_ctor_set(v___x_2746_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2746_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
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
    mut v_preNode_2754_: *mut LeanObject,
    mut v_postNode_2755_: *mut LeanObject,
    mut v___x_2756_: *mut LeanObject,
    mut v_x_2757_: *mut LeanObject,
    mut v_x_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2757_) == 0 {
                    lean_dec(v___x_2756_);
                    lean_dec_ref(v_postNode_2755_);
                    lean_dec_ref(v_preNode_2754_);
                    v___x_2762_ = l_List_reverse___redArg(v_x_2758_);
                    v___x_2763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2763_, 0, v___x_2762_);
                    return v___x_2763_;
                } else {
                    v_head_2764_ = lean_ctor_get(v_x_2757_, 0);
                    v_tail_2765_ = lean_ctor_get(v_x_2757_, 1);
                    v_isSharedCheck_2783_ = (!lean_is_exclusive(v_x_2757_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2767_ = v_x_2757_;
                        v_isShared_2768_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2765_);
                        lean_inc(v_head_2764_);
                        lean_dec(v_x_2757_);
                        v___x_2767_ = lean_box(0);
                        v_isShared_2768_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_2756_);
                lean_inc_ref(v_postNode_2755_);
                lean_inc_ref(v_preNode_2754_);
                v___x_2769_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2754_, v_postNode_2755_, v___x_2756_, v_head_2764_, v___y_2759_, v___y_2760_);
                if lean_obj_tag(v___x_2769_) == 0 {
                    v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
                    lean_inc(v_a_2770_);
                    lean_dec_ref_known(v___x_2769_, 1);
                    if v_isShared_2768_ == 0 {
                        lean_ctor_set(v___x_2767_, 1, v_x_2758_);
                        lean_ctor_set(v___x_2767_, 0, v_a_2770_);
                        v___x_2772_ = v___x_2767_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2770_);
                        lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_x_2758_);
                        v___x_2772_ = v_reuseFailAlloc_2774_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2767_);
                    lean_dec(v_tail_2765_);
                    lean_dec(v_x_2758_);
                    lean_dec(v___x_2756_);
                    lean_dec_ref(v_postNode_2755_);
                    lean_dec_ref(v_preNode_2754_);
                    v_a_2775_ = lean_ctor_get(v___x_2769_, 0);
                    v_isSharedCheck_2782_ = (!lean_is_exclusive(v___x_2769_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v___x_2777_ = v___x_2769_;
                        v_isShared_2778_ = v_isSharedCheck_2782_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2775_);
                        lean_dec(v___x_2769_);
                        v___x_2777_ = lean_box(0);
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
                    v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
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
    mut v_preNode_2784_: *mut LeanObject,
    mut v_postNode_2785_: *mut LeanObject,
    mut v___x_2786_: *mut LeanObject,
    mut v_x_2787_: *mut LeanObject,
    mut v_x_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_2784_, v_postNode_2785_, v___x_2786_, v_x_2787_, v_x_2788_, v___y_2789_, v___y_2790_);
    lean_dec(v___y_2790_);
    lean_dec_ref(v___y_2789_);
    return v_res_2792_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(
    mut v_preNode_2793_: *mut LeanObject,
    mut v_postNode_2794_: *mut LeanObject,
    mut v_x_2795_: *mut LeanObject,
    mut v_x_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
    mut v___y_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_res_2800_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2793_, v_postNode_2794_, v_x_2795_, v_x_2796_, v___y_2797_, v___y_2798_);
    lean_dec(v___y_2798_);
    lean_dec_ref(v___y_2797_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(
    mut v_preNode_2801_: *mut LeanObject,
    mut v_postNode_2802_: *mut LeanObject,
    mut v_ctx_x3f_2803_: *mut LeanObject,
    mut v_t_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_unused_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2808_ = lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2808_, 0, v_postNode_2802_);
                v___x_2809_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_2801_, v___f_2808_, v_ctx_x3f_2803_, v_t_2804_, v___y_2805_, v___y_2806_);
                if lean_obj_tag(v___x_2809_) == 0 {
                    v_isSharedCheck_2817_ = (!lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v_unused_2818_ = lean_ctor_get(v___x_2809_, 0);
                        lean_dec(v_unused_2818_);
                        v___x_2811_ = v___x_2809_;
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2809_);
                        v___x_2811_ = lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2819_ = lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2826_ = (!lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2826_ == 0 {
                        v___x_2821_ = v___x_2809_;
                        v_isShared_2822_ = v_isSharedCheck_2826_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2819_);
                        lean_dec(v___x_2809_);
                        v___x_2821_ = lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2826_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2813_ = lean_box(0);
                if v_isShared_2812_ == 0 {
                    lean_ctor_set(v___x_2811_, 0, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
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
                    v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
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
    mut v_preNode_2827_: *mut LeanObject,
    mut v_postNode_2828_: *mut LeanObject,
    mut v_ctx_x3f_2829_: *mut LeanObject,
    mut v_t_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2834_: *mut LeanObject = core::ptr::null_mut();
    v_res_2834_ =
        l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(
            v_preNode_2827_,
            v_postNode_2828_,
            v_ctx_x3f_2829_,
            v_t_2830_,
            v___y_2831_,
            v___y_2832_,
        );
    lean_dec(v___y_2832_);
    lean_dec_ref(v___y_2831_);
    return v_res_2834_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(
    mut v___x_2835_: u8,
    mut v_val_2836_: *mut LeanObject,
    mut v_val_2837_: *mut LeanObject,
    mut v_as_2838_: *mut LeanObject,
    mut v_sz_2839_: usize,
    mut v_i_2840_: usize,
    mut v_b_2841_: *mut LeanObject,
    mut v___y_2842_: *mut LeanObject,
    mut v___y_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2845_: u8 = 0;
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: usize = 0;
    let mut v___x_2856_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2845_ = lean_usize_dec_lt(v_i_2840_, v_sz_2839_);
                if v___x_2845_ == 0 {
                    lean_dec_ref(v_val_2837_);
                    lean_dec(v_val_2836_);
                    v___x_2846_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2846_, 0, v_b_2841_);
                    return v___x_2846_;
                } else {
                    v___x_2847_ = lean_box((v___x_2835_) as usize);
                    v___f_2848_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___f_2848_, 0, v___x_2847_);
                    v___x_2849_ = l_Lean_Linter_linter_constructorNameAsVariable;
                    v___x_2850_ = lean_box(0);
                    lean_inc_ref(v_val_2837_);
                    lean_inc(v_val_2836_);
                    v___f_2851_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed as *mut core::ffi::c_void, 10, 4);
                    lean_closure_set(v___f_2851_, 0, v_val_2836_);
                    lean_closure_set(v___f_2851_, 1, v___x_2850_);
                    lean_closure_set(v___f_2851_, 2, v_val_2837_);
                    lean_closure_set(v___f_2851_, 3, v___x_2849_);
                    v_a_2852_ = lean_array_uget_borrowed(v_as_2838_, v_i_2840_);
                    v___x_2853_ = lean_box(0);
                    lean_inc(v_a_2852_);
                    v___x_2854_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_2848_, v___f_2851_, v___x_2853_, v_a_2852_, v___y_2842_, v___y_2843_);
                    if lean_obj_tag(v___x_2854_) == 0 {
                        lean_dec_ref_known(v___x_2854_, 1);
                        v___x_2855_ = 1usize;
                        v___x_2856_ = lean_usize_add(v_i_2840_, v___x_2855_);
                        v_i_2840_ = v___x_2856_;
                        v_b_2841_ = v___x_2850_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_val_2837_);
                        lean_dec(v_val_2836_);
                        return v___x_2854_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(
    mut v___x_2858_: *mut LeanObject,
    mut v_val_2859_: *mut LeanObject,
    mut v_val_2860_: *mut LeanObject,
    mut v_as_2861_: *mut LeanObject,
    mut v_sz_2862_: *mut LeanObject,
    mut v_i_2863_: *mut LeanObject,
    mut v_b_2864_: *mut LeanObject,
    mut v___y_2865_: *mut LeanObject,
    mut v___y_2866_: *mut LeanObject,
    mut v___y_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23432__boxed_2868_: u8 = 0;
    let mut v_sz_boxed_2869_: usize = 0;
    let mut v_i_boxed_2870_: usize = 0;
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v___x_23432__boxed_2868_ = (lean_unbox(v___x_2858_) as u8);
    v_sz_boxed_2869_ = lean_unbox_usize(v_sz_2862_);
    lean_dec(v_sz_2862_);
    v_i_boxed_2870_ = lean_unbox_usize(v_i_2863_);
    lean_dec(v_i_2863_);
    v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23432__boxed_2868_, v_val_2859_, v_val_2860_, v_as_2861_, v_sz_boxed_2869_, v_i_boxed_2870_, v_b_2864_, v___y_2865_, v___y_2866_);
    lean_dec(v___y_2866_);
    lean_dec_ref(v___y_2865_);
    lean_dec_ref(v_as_2861_);
    return v_res_2871_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(
    mut v_x_2872_: *mut LeanObject,
    mut v_x_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2873_) == 0 {
                    return v_x_2872_;
                } else {
                    v_key_2874_ = lean_ctor_get(v_x_2873_, 0);
                    v_value_2875_ = lean_ctor_get(v_x_2873_, 1);
                    v_tail_2876_ = lean_ctor_get(v_x_2873_, 2);
                    lean_inc(v_value_2875_);
                    lean_inc(v_key_2874_);
                    v___x_2877_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2877_, 0, v_key_2874_);
                    lean_ctor_set(v___x_2877_, 1, v_value_2875_);
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
    mut v_x_2880_: *mut LeanObject,
    mut v_x_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2882_: *mut LeanObject = core::ptr::null_mut();
    v_res_2882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_2880_, v_x_2881_);
    lean_dec(v_x_2881_);
    return v_res_2882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(
    mut v_as_2883_: *mut LeanObject,
    mut v_i_2884_: usize,
    mut v_stop_2885_: usize,
    mut v_b_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_2893_: *mut LeanObject,
    mut v_i_2894_: *mut LeanObject,
    mut v_stop_2895_: *mut LeanObject,
    mut v_b_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2897_: usize = 0;
    let mut v_stop_boxed_2898_: usize = 0;
    let mut v_res_2899_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2897_ = lean_unbox_usize(v_i_2894_);
    lean_dec(v_i_2894_);
    v_stop_boxed_2898_ = lean_unbox_usize(v_stop_2895_);
    lean_dec(v_stop_2895_);
    v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_2893_, v_i_boxed_2897_, v_stop_boxed_2898_, v_b_2896_);
    lean_dec_ref(v_as_2893_);
    return v_res_2899_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(
    mut v___y_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    v___x_2903_ = lean_st_ref_get(v___y_2901_);
    v_scopes_2904_ = lean_ctor_get(v___x_2903_, 2);
    lean_inc(v_scopes_2904_);
    lean_dec(v___x_2903_);
    v___x_2905_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2906_ = l_List_head_x21___redArg(v___x_2905_, v_scopes_2904_);
    lean_dec(v_scopes_2904_);
    v_opts_2907_ = lean_ctor_get(v___x_2906_, 1);
    lean_inc_ref(v_opts_2907_);
    lean_dec(v___x_2906_);
    v___x_2908_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_2907_, v___y_2901_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2912_: *mut LeanObject = core::ptr::null_mut();
    v_res_2912_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(
            v___y_2909_,
            v___y_2910_,
        );
    lean_dec(v___y_2910_);
    lean_dec_ref(v___y_2909_);
    return v_res_2912_;
}
pub unsafe fn _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0() -> *mut LeanObject
{
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    v___x_2913_ = lean_box(0);
    v___x_2914_ = lean_unsigned_to_nat(16);
    v___x_2915_ = lean_mk_array(v___x_2914_, v___x_2913_);
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    v___x_2916_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once),
        _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0,
    );
    v___x_2917_ = lean_unsigned_to_nat(0);
    v___x_2918_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2918_, 0, v___x_2917_);
    lean_ctor_set(v___x_2918_, 1, v___x_2916_);
    return v___x_2918_;
}
pub unsafe fn l_Lean_Linter_constructorNameAsVariable___lam__0(
    mut v_cmdStx_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2945_: usize = 0;
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2951_: usize = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_unused_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v___y_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: u8 = 0;
    let mut v_size_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: usize = 0;
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2923_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_2920_, v___y_2921_);
                v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
                v_isSharedCheck_2994_ = (!lean_is_exclusive(v___x_2923_)) as u8;
                if v_isSharedCheck_2994_ == 0 {
                    v___x_2926_ = v___x_2923_;
                    v_isShared_2927_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2924_);
                    lean_dec(v___x_2923_);
                    v___x_2926_ = lean_box(0);
                    v_isShared_2927_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2928_ = l_Lean_Linter_linter_constructorNameAsVariable;
                v___x_2929_ = l_Lean_Linter_getLinterValue(v___x_2928_, v_a_2924_);
                lean_dec(v_a_2924_);
                if v___x_2929_ == 0 {
                    v___x_2930_ = lean_box(0);
                    if v_isShared_2927_ == 0 {
                        lean_ctor_set(v___x_2926_, 0, v___x_2930_);
                        v___x_2932_ = v___x_2926_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
                        v___x_2932_ = v_reuseFailAlloc_2933_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2934_ = 0;
                    v___x_2935_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_2919_, v___x_2934_);
                    if lean_obj_tag(v___x_2935_) == 1 {
                        lean_del_object(v___x_2926_);
                        v_val_2936_ = lean_ctor_get(v___x_2935_, 0);
                        lean_inc(v_val_2936_);
                        lean_dec_ref_known(v___x_2935_, 1);
                        v___x_2937_ = lean_st_ref_get(v___y_2921_);
                        v___x_2938_ = lean_unsigned_to_nat(0);
                        v___x_2939_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1,
                        );
                        v___x_2940_ = lean_st_mk_ref(v___x_2939_);
                        v_infoState_2941_ = lean_ctor_get(v___x_2937_, 8);
                        lean_inc_ref(v_infoState_2941_);
                        lean_dec(v___x_2937_);
                        v_trees_2942_ = lean_ctor_get(v_infoState_2941_, 2);
                        lean_inc_ref(v_trees_2942_);
                        lean_dec_ref(v_infoState_2941_);
                        v___x_2943_ = l_Lean_PersistentArray_toArray___redArg(v_trees_2942_);
                        lean_dec_ref(v_trees_2942_);
                        v___x_2944_ = lean_box(0);
                        v_sz_2945_ = lean_array_size(v___x_2943_);
                        v___x_2946_ = 0usize;
                        lean_inc(v___x_2940_);
                        v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_2929_, v___x_2940_, v_val_2936_, v___x_2943_, v_sz_2945_, v___x_2946_, v___x_2944_, v___y_2920_, v___y_2921_);
                        lean_dec_ref(v___x_2943_);
                        if lean_obj_tag(v___x_2947_) == 0 {
                            lean_dec_ref_known(v___x_2947_, 1);
                            v___x_2948_ = lean_st_ref_get(v___x_2940_);
                            lean_dec(v___x_2940_);
                            v_size_2980_ = lean_ctor_get(v___x_2948_, 0);
                            lean_inc(v_size_2980_);
                            v_buckets_2981_ = lean_ctor_get(v___x_2948_, 1);
                            lean_inc_ref(v_buckets_2981_);
                            lean_dec(v___x_2948_);
                            v___x_2982_ = lean_mk_empty_array_with_capacity(v_size_2980_);
                            lean_dec(v_size_2980_);
                            v___x_2983_ = lean_array_get_size(v_buckets_2981_);
                            v___x_2984_ = lean_nat_dec_lt(v___x_2938_, v___x_2983_);
                            if v___x_2984_ == 0 {
                                lean_dec_ref(v_buckets_2981_);
                                v___y_2974_ = v___x_2982_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2985_ = lean_nat_dec_le(v___x_2983_, v___x_2983_);
                                if v___x_2985_ == 0 {
                                    if v___x_2984_ == 0 {
                                        lean_dec_ref(v_buckets_2981_);
                                        v___y_2974_ = v___x_2982_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_2986_ = lean_usize_of_nat(v___x_2983_);
                                        v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_2981_, v___x_2946_, v___x_2986_, v___x_2982_);
                                        lean_dec_ref(v_buckets_2981_);
                                        v___y_2974_ = v___x_2987_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v___x_2988_ = lean_usize_of_nat(v___x_2983_);
                                    v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_2981_, v___x_2946_, v___x_2988_, v___x_2982_);
                                    lean_dec_ref(v_buckets_2981_);
                                    v___y_2974_ = v___x_2989_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2940_);
                            return v___x_2947_;
                        }
                    } else {
                        lean_dec(v___x_2935_);
                        v___x_2990_ = lean_box(0);
                        if v_isShared_2927_ == 0 {
                            lean_ctor_set(v___x_2926_, 0, v___x_2990_);
                            v___x_2992_ = v___x_2926_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
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
                lean_dec_ref(v___y_2950_);
                if lean_obj_tag(v___x_2952_) == 0 {
                    v_isSharedCheck_2959_ = (!lean_is_exclusive(v___x_2952_)) as u8;
                    if v_isSharedCheck_2959_ == 0 {
                        v_unused_2960_ = lean_ctor_get(v___x_2952_, 0);
                        lean_dec(v_unused_2960_);
                        v___x_2954_ = v___x_2952_;
                        v_isShared_2955_ = v_isSharedCheck_2959_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2952_);
                        v___x_2954_ = lean_box(0);
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
                    lean_ctor_set(v___x_2954_, 0, v___x_2944_);
                    v___x_2957_ = v___x_2954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2944_);
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
                lean_dec(v___y_2965_);
                lean_dec(v___y_2962_);
                v___y_2950_ = v___x_2966_;
                state = 3;
                continue;
            }
            7 => {
                v___x_2972_ = lean_nat_dec_le(v___y_2971_, v___y_2969_);
                if v___x_2972_ == 0 {
                    lean_dec(v___y_2969_);
                    lean_inc(v___y_2971_);
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
                    v___x_2977_ = lean_unsigned_to_nat(1);
                    v___x_2978_ = lean_nat_sub(v___x_2975_, v___x_2977_);
                    v___x_2979_ = lean_nat_dec_le(v___x_2938_, v___x_2978_);
                    if v___x_2979_ == 0 {
                        lean_inc(v___x_2978_);
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
    mut v_cmdStx_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ =
        l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_2995_, v___y_2996_, v___y_2997_);
    lean_dec(v___y_2997_);
    lean_dec_ref(v___y_2996_);
    lean_dec(v_cmdStx_2995_);
    return v_res_2999_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(
    mut v_00_u03b2_3009_: *mut LeanObject,
    mut v_m_3010_: *mut LeanObject,
    mut v_a_3011_: *mut LeanObject,
) -> u8 {
    let mut v___x_3012_: u8 = 0;
    v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_3010_, v_a_3011_);
    return v___x_3012_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(
    mut v_00_u03b2_3013_: *mut LeanObject,
    mut v_m_3014_: *mut LeanObject,
    mut v_a_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3016_: u8 = 0;
    let mut v_r_3017_: *mut LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_3013_, v_m_3014_, v_a_3015_);
    lean_dec_ref(v_a_3015_);
    lean_dec_ref(v_m_3014_);
    v_r_3017_ = lean_box((v_res_3016_) as usize);
    return v_r_3017_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(
    mut v_00_u03b2_3018_: *mut LeanObject,
    mut v_m_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_b_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    v___x_3022_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_3019_, v_a_3020_, v_b_3021_);
    return v___x_3022_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(
    mut v_str_3023_: *mut LeanObject,
    mut v_val_3024_: *mut LeanObject,
    mut v_info_3025_: *mut LeanObject,
    mut v___x_3026_: *mut LeanObject,
    mut v_val_3027_: *mut LeanObject,
    mut v___x_3028_: u8,
    mut v_as_3029_: *mut LeanObject,
    mut v_as_x27_3030_: *mut LeanObject,
    mut v_b_3031_: *mut LeanObject,
    mut v_a_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_str_3037_: *mut LeanObject,
    mut v_val_3038_: *mut LeanObject,
    mut v_info_3039_: *mut LeanObject,
    mut v___x_3040_: *mut LeanObject,
    mut v_val_3041_: *mut LeanObject,
    mut v___x_3042_: *mut LeanObject,
    mut v_as_3043_: *mut LeanObject,
    mut v_as_x27_3044_: *mut LeanObject,
    mut v_b_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23724__boxed_3050_: u8 = 0;
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v___x_23724__boxed_3050_ = (lean_unbox(v___x_3042_) as u8);
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
    lean_dec(v___y_3048_);
    lean_dec_ref(v___y_3047_);
    lean_dec(v_as_x27_3044_);
    lean_dec(v_as_3043_);
    lean_dec_ref(v_info_3039_);
    lean_dec(v_val_3038_);
    lean_dec_ref(v_str_3037_);
    return v_res_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(
    mut v_n_3052_: *mut LeanObject,
    mut v_as_3053_: *mut LeanObject,
    mut v_lo_3054_: *mut LeanObject,
    mut v_hi_3055_: *mut LeanObject,
    mut v_w_3056_: *mut LeanObject,
    mut v_hlo_3057_: *mut LeanObject,
    mut v_hhi_3058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    v___x_3059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_3052_, v_as_3053_, v_lo_3054_, v_hi_3055_);
    return v___x_3059_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(
    mut v_n_3060_: *mut LeanObject,
    mut v_as_3061_: *mut LeanObject,
    mut v_lo_3062_: *mut LeanObject,
    mut v_hi_3063_: *mut LeanObject,
    mut v_w_3064_: *mut LeanObject,
    mut v_hlo_3065_: *mut LeanObject,
    mut v_hhi_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_3060_, v_as_3061_, v_lo_3062_, v_hi_3063_, v_w_3064_, v_hlo_3065_, v_hhi_3066_);
    lean_dec(v_hi_3063_);
    lean_dec(v_n_3060_);
    return v_res_3067_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(
    mut v_00_u03b2_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
) -> u8 {
    let mut v___x_3071_: u8 = 0;
    v___x_3071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_3069_, v_x_3070_);
    return v___x_3071_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(
    mut v_00_u03b2_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_x_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3075_: u8 = 0;
    let mut v_r_3076_: *mut LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_3072_, v_a_3073_, v_x_3074_);
    lean_dec(v_x_3074_);
    lean_dec_ref(v_a_3073_);
    v_r_3076_ = lean_box((v_res_3075_) as usize);
    return v_r_3076_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(
    mut v_00_u03b2_3077_: *mut LeanObject,
    mut v_data_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_3078_);
    return v___x_3079_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(
    mut v_00_u03b2_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_b_3082_: *mut LeanObject,
    mut v_x_3083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_3081_, v_b_3082_, v_x_3083_);
    return v___x_3084_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(
    mut v_00_u03b1_3085_: *mut LeanObject,
    mut v_msg_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_3086_, v___y_3087_, v___y_3088_);
    return v___x_3090_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(
    mut v_00_u03b1_3091_: *mut LeanObject,
    mut v_msg_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3096_: *mut LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_3091_, v_msg_3092_, v___y_3093_, v___y_3094_);
    lean_dec(v___y_3094_);
    lean_dec_ref(v___y_3093_);
    return v_res_3096_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(
    mut v_00_u03b1_3097_: *mut LeanObject,
    mut v_preNode_3098_: *mut LeanObject,
    mut v_postNode_3099_: *mut LeanObject,
    mut v_x_3100_: *mut LeanObject,
    mut v_x_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    v___x_3105_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_3098_, v_postNode_3099_, v_x_3100_, v_x_3101_, v___y_3102_, v___y_3103_);
    return v___x_3105_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(
    mut v_00_u03b1_3106_: *mut LeanObject,
    mut v_preNode_3107_: *mut LeanObject,
    mut v_postNode_3108_: *mut LeanObject,
    mut v_x_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3114_: *mut LeanObject = core::ptr::null_mut();
    v_res_3114_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_3106_, v_preNode_3107_, v_postNode_3108_, v_x_3109_, v_x_3110_, v___y_3111_, v___y_3112_);
    lean_dec(v___y_3112_);
    lean_dec_ref(v___y_3111_);
    return v_res_3114_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(
    mut v_n_3115_: *mut LeanObject,
    mut v_lo_3116_: *mut LeanObject,
    mut v_hi_3117_: *mut LeanObject,
    mut v_hhi_3118_: *mut LeanObject,
    mut v_pivot_3119_: *mut LeanObject,
    mut v_as_3120_: *mut LeanObject,
    mut v_i_3121_: *mut LeanObject,
    mut v_k_3122_: *mut LeanObject,
    mut v_ilo_3123_: *mut LeanObject,
    mut v_ik_3124_: *mut LeanObject,
    mut v_w_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    v___x_3126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_3117_, v_pivot_3119_, v_as_3120_, v_i_3121_, v_k_3122_);
    return v___x_3126_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(
    mut v_n_3127_: *mut LeanObject,
    mut v_lo_3128_: *mut LeanObject,
    mut v_hi_3129_: *mut LeanObject,
    mut v_hhi_3130_: *mut LeanObject,
    mut v_pivot_3131_: *mut LeanObject,
    mut v_as_3132_: *mut LeanObject,
    mut v_i_3133_: *mut LeanObject,
    mut v_k_3134_: *mut LeanObject,
    mut v_ilo_3135_: *mut LeanObject,
    mut v_ik_3136_: *mut LeanObject,
    mut v_w_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3138_: *mut LeanObject = core::ptr::null_mut();
    v_res_3138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_3127_, v_lo_3128_, v_hi_3129_, v_hhi_3130_, v_pivot_3131_, v_as_3132_, v_i_3133_, v_k_3134_, v_ilo_3135_, v_ik_3136_, v_w_3137_);
    lean_dec_ref(v_pivot_3131_);
    lean_dec(v_hi_3129_);
    lean_dec(v_lo_3128_);
    lean_dec(v_n_3127_);
    return v_res_3138_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(
    mut v_00_u03b2_3139_: *mut LeanObject,
    mut v_i_3140_: *mut LeanObject,
    mut v_source_3141_: *mut LeanObject,
    mut v_target_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    v___x_3143_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_3140_, v_source_3141_, v_target_3142_);
    return v___x_3143_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(
    mut v_00_u03b1_3144_: *mut LeanObject,
    mut v_preNode_3145_: *mut LeanObject,
    mut v_postNode_3146_: *mut LeanObject,
    mut v___x_3147_: *mut LeanObject,
    mut v_x_3148_: *mut LeanObject,
    mut v_x_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v___x_3153_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_3145_, v_postNode_3146_, v___x_3147_, v_x_3148_, v_x_3149_, v___y_3150_, v___y_3151_);
    return v___x_3153_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(
    mut v_00_u03b1_3154_: *mut LeanObject,
    mut v_preNode_3155_: *mut LeanObject,
    mut v_postNode_3156_: *mut LeanObject,
    mut v___x_3157_: *mut LeanObject,
    mut v_x_3158_: *mut LeanObject,
    mut v_x_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3163_: *mut LeanObject = core::ptr::null_mut();
    v_res_3163_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_3154_, v_preNode_3155_, v_postNode_3156_, v___x_3157_, v_x_3158_, v_x_3159_, v___y_3160_, v___y_3161_);
    lean_dec(v___y_3161_);
    lean_dec_ref(v___y_3160_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(
    mut v_msgData_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_3164_, v___y_3166_);
    return v___x_3168_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(
    mut v_msgData_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3173_: *mut LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_3169_, v___y_3170_, v___y_3171_);
    lean_dec(v___y_3171_);
    lean_dec_ref(v___y_3170_);
    return v_res_3173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(
    mut v_00_u03b2_3174_: *mut LeanObject,
    mut v_x_3175_: *mut LeanObject,
    mut v_x_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    v___x_3177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_3175_, v_x_3176_);
    return v___x_3177_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_Linter_constructorNameAsVariable;
    v___x_3180_ = l_Lean_Elab_Command_addLinter(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(
    mut v_a_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3182_: *mut LeanObject = core::ptr::null_mut();
    v_res_3182_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
    return v_res_3182_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_ConstructorAsVariable(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_constructorNameAsVariable = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_constructorNameAsVariable);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_ConstructorAsVariable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_ConstructorAsVariable(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_ConstructorAsVariable(builtin);
}
