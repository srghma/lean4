// Lean compiler output
// Module: Lean.Linter.TacticTypeCheck
// Imports: Lean.Elab.Command Lean.Linter.Util Lean.Meta.Check Lean.Meta.Diagnostics
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_toArray___redArg, l_Lean_PersistentArray_toList___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
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
    l_Lean_Elab_ContextInfo_runMetaM___redArg, l_Lean_Elab_Info_updateContext_x3f,
    l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::Linter::Init::l_Lean_Linter_linterMessageTag;
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp;
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_check, runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::Meta::Diagnostics::{
    initialize_Lean_Meta_Diagnostics, runtime_initialize_Lean_Meta_Diagnostics,
};
use crate::r#gen::Lean::Meta::Instances::l_Lean_Meta_isInstanceCore;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findDecl_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::ReducibilityAttrs::lean_get_reducibility_status;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [116, 97, 99, 116, 105, 99, 67, 104, 101, 99, 107, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3877803915353198398 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 108, 105, 110, 116, 101, 114, 32, 116, 104, 97, 116, 32, 116, 121, 112, 101, 45, 99, 104, 101, 99, 107, 115, 32, 101, 118, 101, 114, 121, 32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4424989899264441540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [84, 97, 99, 116, 105, 99, 84, 121, 112, 101, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10581205489494877745 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1816322908595936884 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1896795829154494325 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8582532011273483831 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3028325180435466294 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3528273497824055570 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 105, 116, 105, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 100, 117, 99, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101, 45, 99, 111, 114, 114, 101, 99, 116, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 59, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [32, 115, 111, 109, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 97, 115, 32, 96, 64, 91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 58, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [10, 70, 117, 108, 108, 32, 101, 114, 114, 111, 114, 58, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 111, 114, 32, 109, 97, 114, 107, 105, 110, 103, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 111, 110, 115, 105, 100, 101, 114, 32, 114, 101, 112, 104, 114, 97, 115, 105, 110, 103, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 111, 114, 32, 109, 97, 114, 107, 105, 110, 103, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16625058045004708007 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(
    mut v_name_2123_: *mut crate::leanh::LeanObject,
    mut v_decl_2124_: *mut crate::leanh::LeanObject,
    mut v_ref_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_unused_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2127_ = crate::leanh::lean_ctor_get(v_decl_2124_, 0);
                v_descr_2128_ = crate::leanh::lean_ctor_get(v_decl_2124_, 1);
                v_deprecation_x3f_2129_ = crate::leanh::lean_ctor_get(v_decl_2124_, 2);
                v___x_2130_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2131_ = (crate::leanh::lean_unbox(v_defValue_2127_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_2130_, 0 as u32, v___x_2131_);
                crate::leanh::lean_inc(v_deprecation_x3f_2129_);
                crate::leanh::lean_inc_ref(v_descr_2128_);
                crate::leanh::lean_inc_n(v_name_2123_, 2);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v_name_2123_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v_ref_2125_);
                crate::leanh::lean_ctor_set(v___x_2132_, 2, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2132_, 3, v_descr_2128_);
                crate::leanh::lean_ctor_set(v___x_2132_, 4, v_deprecation_x3f_2129_);
                v___x_2133_ = lean_register_option(v_name_2123_, v___x_2132_);
                if crate::leanh::lean_obj_tag(v___x_2133_) == 0 {
                    v_isSharedCheck_2141_ = (!crate::leanh::lean_is_exclusive(v___x_2133_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v_unused_2142_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                        crate::leanh::lean_dec(v_unused_2142_);
                        v___x_2135_ = v___x_2133_;
                        v_isShared_2136_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2133_);
                        v___x_2135_ = crate::leanh::lean_box(0);
                        v_isShared_2136_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2123_);
                    v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                    v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v___x_2133_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2133_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2143_);
                        crate::leanh::lean_dec(v___x_2133_);
                        v___x_2145_ = crate::leanh::lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_2127_);
                v___x_2137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2137_, 0, v_name_2123_);
                crate::leanh::lean_ctor_set(v___x_2137_, 1, v_defValue_2127_);
                if v_isShared_2136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2137_);
                    v___x_2139_ = v___x_2135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
                    v___x_2139_ = v_reuseFailAlloc_2140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2139_;
            }
            3 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2151_: *mut crate::leanh::LeanObject,
    mut v_decl_2152_: *mut crate::leanh::LeanObject,
    mut v_ref_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v_name_2151_, v_decl_2152_, v_ref_2153_);
    crate::leanh::lean_dec_ref(v_decl_2152_);
    return v_res_2155_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2200_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2201_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2202_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v___x_2199_, v___x_2200_, v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4____boxed(
    mut v_a_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
    return v_res_2204_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(
    mut v_e_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2208_ = l_Lean_Expr_hasMVar(v_e_2205_);
                if v___x_2208_ == 0 {
                    v___x_2209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2209_, 0, v_e_2205_);
                    return v___x_2209_;
                } else {
                    v___x_2210_ = lean_st_ref_get(v___y_2206_);
                    v_mctx_2211_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2211_);
                    crate::leanh::lean_dec(v___x_2210_);
                    v___x_2212_ = l_Lean_instantiateMVarsCore(v_mctx_2211_, v_e_2205_);
                    v_fst_2213_ = crate::leanh::lean_ctor_get(v___x_2212_, 0);
                    crate::leanh::lean_inc(v_fst_2213_);
                    v_snd_2214_ = crate::leanh::lean_ctor_get(v___x_2212_, 1);
                    crate::leanh::lean_inc(v_snd_2214_);
                    crate::leanh::lean_dec_ref(v___x_2212_);
                    v___x_2215_ = lean_st_ref_take(v___y_2206_);
                    v_cache_2216_ = crate::leanh::lean_ctor_get(v___x_2215_, 1);
                    v_zetaDeltaFVarIds_2217_ = crate::leanh::lean_ctor_get(v___x_2215_, 2);
                    v_postponed_2218_ = crate::leanh::lean_ctor_get(v___x_2215_, 3);
                    v_diag_2219_ = crate::leanh::lean_ctor_get(v___x_2215_, 4);
                    v_isSharedCheck_2228_ = (!crate::leanh::lean_is_exclusive(v___x_2215_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v_unused_2229_ = crate::leanh::lean_ctor_get(v___x_2215_, 0);
                        crate::leanh::lean_dec(v_unused_2229_);
                        v___x_2221_ = v___x_2215_;
                        v_isShared_2222_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2219_);
                        crate::leanh::lean_inc(v_postponed_2218_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2217_);
                        crate::leanh::lean_inc(v_cache_2216_);
                        crate::leanh::lean_dec(v___x_2215_);
                        v___x_2221_ = crate::leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2221_, 0, v_snd_2214_);
                    v___x_2224_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_snd_2214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_cache_2216_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2227_,
                        2,
                        v_zetaDeltaFVarIds_2217_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_postponed_2218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_diag_2219_);
                    v___x_2224_ = v_reuseFailAlloc_2227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2225_ = lean_st_ref_set(v___y_2206_, v___x_2224_);
                v___x_2226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2226_, 0, v_fst_2213_);
                return v___x_2226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg___boxed(
    mut v_e_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_2230_, v___y_2231_);
    crate::leanh::lean_dec(v___y_2231_);
    return v_res_2233_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(
    mut v_e_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_2234_, v___y_2236_);
    return v___x_2240_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___boxed(
    mut v_e_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(v_e_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
    crate::leanh::lean_dec(v___y_2245_);
    crate::leanh::lean_dec_ref(v___y_2244_);
    crate::leanh::lean_dec(v___y_2243_);
    crate::leanh::lean_dec_ref(v___y_2242_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(
    mut v_opts_2248_: *mut crate::leanh::LeanObject,
    mut v_opt_2249_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2250_ = crate::leanh::lean_ctor_get(v_opt_2249_, 0);
    v_defValue_2251_ = crate::leanh::lean_ctor_get(v_opt_2249_, 1);
    v_map_2252_ = crate::leanh::lean_ctor_get(v_opts_2248_, 0);
    v___x_2253_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2252_,
            v_name_2250_,
        );
    if crate::leanh::lean_obj_tag(v___x_2253_) == 0 {
        let mut v___x_2254_: u8 = 0;
        v___x_2254_ = (crate::leanh::lean_unbox(v_defValue_2251_) as u8);
        return v___x_2254_;
    } else {
        let mut v_val_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2255_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
        crate::leanh::lean_inc(v_val_2255_);
        crate::leanh::lean_dec_ref_known(v___x_2253_, 1);
        if crate::leanh::lean_obj_tag(v_val_2255_) == 1 {
            let mut v_v_2256_: u8 = 0;
            v_v_2256_ = crate::leanh::lean_ctor_get_uint8(v_val_2255_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2255_, 0);
            return v_v_2256_;
        } else {
            let mut v___x_2257_: u8 = 0;
            crate::leanh::lean_dec(v_val_2255_);
            v___x_2257_ = (crate::leanh::lean_unbox(v_defValue_2251_) as u8);
            return v___x_2257_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(
    mut v_opts_2258_: *mut crate::leanh::LeanObject,
    mut v_opt_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: u8 = 0;
    let mut v_r_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2258_, v_opt_2259_);
    crate::leanh::lean_dec_ref(v_opt_2259_);
    crate::leanh::lean_dec_ref(v_opts_2258_);
    v_r_2261_ = crate::leanh::lean_box((v_res_2260_) as usize);
    return v_r_2261_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(
    mut v_opts_2262_: *mut crate::leanh::LeanObject,
    mut v_opt_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2264_ = crate::leanh::lean_ctor_get(v_opt_2263_, 0);
    v_defValue_2265_ = crate::leanh::lean_ctor_get(v_opt_2263_, 1);
    v_map_2266_ = crate::leanh::lean_ctor_get(v_opts_2262_, 0);
    v___x_2267_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2266_,
            v_name_2264_,
        );
    if crate::leanh::lean_obj_tag(v___x_2267_) == 0 {
        crate::leanh::lean_inc(v_defValue_2265_);
        return v_defValue_2265_;
    } else {
        let mut v_val_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2268_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
        crate::leanh::lean_inc(v_val_2268_);
        crate::leanh::lean_dec_ref_known(v___x_2267_, 1);
        if crate::leanh::lean_obj_tag(v_val_2268_) == 3 {
            let mut v_v_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_2269_ = crate::leanh::lean_ctor_get(v_val_2268_, 0);
            crate::leanh::lean_inc(v_v_2269_);
            crate::leanh::lean_dec_ref_known(v_val_2268_, 1);
            return v_v_2269_;
        } else {
            crate::leanh::lean_dec(v_val_2268_);
            crate::leanh::lean_inc(v_defValue_2265_);
            return v_defValue_2265_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(
    mut v_opts_2270_: *mut crate::leanh::LeanObject,
    mut v_opt_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_opts_2270_, v_opt_2271_);
    crate::leanh::lean_dec_ref(v_opt_2271_);
    crate::leanh::lean_dec_ref(v_opts_2270_);
    return v_res_2272_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(
    mut v_lctx_2273_: *mut crate::leanh::LeanObject,
    mut v_localInsts_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    crate::leanh::lean_box(0),
                    v_lctx_2273_,
                    v_localInsts_2274_,
                    v_x_2275_,
                    v___y_2276_,
                    v___y_2277_,
                    v___y_2278_,
                    v___y_2279_,
                );
                if crate::leanh::lean_obj_tag(v___x_2281_) == 0 {
                    v_a_2282_ = crate::leanh::lean_ctor_get(v___x_2281_, 0);
                    v_isSharedCheck_2289_ = (!crate::leanh::lean_is_exclusive(v___x_2281_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2284_ = v___x_2281_;
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2282_);
                        crate::leanh::lean_dec(v___x_2281_);
                        v___x_2284_ = crate::leanh::lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2281_, 0);
                    v_isSharedCheck_2297_ = (!crate::leanh::lean_is_exclusive(v___x_2281_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v___x_2292_ = v___x_2281_;
                        v_isShared_2293_ = v_isSharedCheck_2297_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2290_);
                        crate::leanh::lean_dec(v___x_2281_);
                        v___x_2292_ = crate::leanh::lean_box(0);
                        v_isShared_2293_ = v_isSharedCheck_2297_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2285_ == 0 {
                    v___x_2287_ = v___x_2284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
                    v___x_2287_ = v_reuseFailAlloc_2288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2287_;
            }
            3 => {
                if v_isShared_2293_ == 0 {
                    v___x_2295_ = v___x_2292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(
    mut v_lctx_2298_: *mut crate::leanh::LeanObject,
    mut v_localInsts_2299_: *mut crate::leanh::LeanObject,
    mut v_x_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2306_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_2298_, v_localInsts_2299_, v_x_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
    crate::leanh::lean_dec(v___y_2304_);
    crate::leanh::lean_dec_ref(v___y_2303_);
    crate::leanh::lean_dec(v___y_2302_);
    crate::leanh::lean_dec_ref(v___y_2301_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(
    mut v_00_u03b1_2307_: *mut crate::leanh::LeanObject,
    mut v_lctx_2308_: *mut crate::leanh::LeanObject,
    mut v_localInsts_2309_: *mut crate::leanh::LeanObject,
    mut v_x_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_2308_, v_localInsts_2309_, v_x_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
    return v___x_2316_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(
    mut v_00_u03b1_2317_: *mut crate::leanh::LeanObject,
    mut v_lctx_2318_: *mut crate::leanh::LeanObject,
    mut v_localInsts_2319_: *mut crate::leanh::LeanObject,
    mut v_x_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_00_u03b1_2317_, v_lctx_2318_, v_localInsts_2319_, v_x_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
    crate::leanh::lean_dec(v___y_2324_);
    crate::leanh::lean_dec_ref(v___y_2323_);
    crate::leanh::lean_dec(v___y_2322_);
    crate::leanh::lean_dec_ref(v___y_2321_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(
    mut v_opt_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = lean_st_ref_get(v___y_2328_);
    v_scopes_2331_ = crate::leanh::lean_ctor_get(v___x_2330_, 2);
    crate::leanh::lean_inc(v_scopes_2331_);
    crate::leanh::lean_dec(v___x_2330_);
    v___x_2332_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2333_ = l_List_head_x21___redArg(v___x_2332_, v_scopes_2331_);
    crate::leanh::lean_dec(v_scopes_2331_);
    v_opts_2334_ = crate::leanh::lean_ctor_get(v___x_2333_, 1);
    crate::leanh::lean_inc_ref(v_opts_2334_);
    crate::leanh::lean_dec(v___x_2333_);
    v___x_2335_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2334_, v_opt_2327_);
    crate::leanh::lean_dec_ref(v_opts_2334_);
    v___x_2336_ = crate::leanh::lean_box((v___x_2335_) as usize);
    v___x_2337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(
    mut v_opt_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_2338_, v___y_2339_);
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v_opt_2338_);
    return v_res_2341_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(
    mut v_a_2342_: u8,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
    mut v_x_2344_: *mut crate::leanh::LeanObject,
    mut v_x_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = crate::leanh::lean_box((v_a_2342_) as usize);
    v___x_2350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed(
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_x_2352_: *mut crate::leanh::LeanObject,
    mut v_x_2353_: *mut crate::leanh::LeanObject,
    mut v_x_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_28976__boxed_2358_: u8 = 0;
    let mut v_res_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_28976__boxed_2358_ = (crate::leanh::lean_unbox(v_a_2351_) as u8);
    v_res_2359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(v_a_28976__boxed_2358_, v_x_2352_, v_x_2353_, v_x_2354_, v___y_2355_, v___y_2356_);
    crate::leanh::lean_dec(v___y_2356_);
    crate::leanh::lean_dec_ref(v___y_2355_);
    crate::leanh::lean_dec_ref(v_x_2354_);
    crate::leanh::lean_dec_ref(v_x_2353_);
    crate::leanh::lean_dec_ref(v_x_2352_);
    return v_res_2359_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(
    mut v_postNode_2360_: *mut crate::leanh::LeanObject,
    mut v_ci_2361_: *mut crate::leanh::LeanObject,
    mut v_i_2362_: *mut crate::leanh::LeanObject,
    mut v_cs_2363_: *mut crate::leanh::LeanObject,
    mut v_x_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2366_);
    crate::leanh::lean_inc_ref(v___y_2365_);
    v___x_2368_ = crate::leanh::lean_apply_6(
        v_postNode_2360_,
        v_ci_2361_,
        v_i_2362_,
        v_cs_2363_,
        v___y_2365_,
        v___y_2366_,
        crate::leanh::lean_box(0),
    );
    return v___x_2368_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(
    mut v_postNode_2369_: *mut crate::leanh::LeanObject,
    mut v_ci_2370_: *mut crate::leanh::LeanObject,
    mut v_i_2371_: *mut crate::leanh::LeanObject,
    mut v_cs_2372_: *mut crate::leanh::LeanObject,
    mut v_x_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_postNode_2369_, v_ci_2370_, v_i_2371_, v_cs_2372_, v_x_2373_, v___y_2374_, v___y_2375_);
    crate::leanh::lean_dec(v___y_2375_);
    crate::leanh::lean_dec_ref(v___y_2374_);
    crate::leanh::lean_dec(v_x_2373_);
    return v_res_2377_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2378_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(
    mut v_msg_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_toFunctor_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___f_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_25987__overap_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v_unused_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2385_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0);
                v___x_2386_ = l_StateRefT_x27_instMonad___redArg(v___x_2385_);
                v_toApplicative_2387_ = crate::leanh::lean_ctor_get(v___x_2386_, 0);
                v_isSharedCheck_2418_ = (!crate::leanh::lean_is_exclusive(v___x_2386_)) as u8;
                if v_isSharedCheck_2418_ == 0 {
                    v_unused_2419_ = crate::leanh::lean_ctor_get(v___x_2386_, 1);
                    crate::leanh::lean_dec(v_unused_2419_);
                    v___x_2389_ = v___x_2386_;
                    v_isShared_2390_ = v_isSharedCheck_2418_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2387_);
                    crate::leanh::lean_dec(v___x_2386_);
                    v___x_2389_ = crate::leanh::lean_box(0);
                    v_isShared_2390_ = v_isSharedCheck_2418_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2391_ = crate::leanh::lean_ctor_get(v_toApplicative_2387_, 0);
                v_toSeq_2392_ = crate::leanh::lean_ctor_get(v_toApplicative_2387_, 2);
                v_toSeqLeft_2393_ = crate::leanh::lean_ctor_get(v_toApplicative_2387_, 3);
                v_toSeqRight_2394_ = crate::leanh::lean_ctor_get(v_toApplicative_2387_, 4);
                v_isSharedCheck_2416_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2387_)) as u8;
                if v_isSharedCheck_2416_ == 0 {
                    v_unused_2417_ = crate::leanh::lean_ctor_get(v_toApplicative_2387_, 1);
                    crate::leanh::lean_dec(v_unused_2417_);
                    v___x_2396_ = v_toApplicative_2387_;
                    v_isShared_2397_ = v_isSharedCheck_2416_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2394_);
                    crate::leanh::lean_inc(v_toSeqLeft_2393_);
                    crate::leanh::lean_inc(v_toSeq_2392_);
                    crate::leanh::lean_inc(v_toFunctor_2391_);
                    crate::leanh::lean_dec(v_toApplicative_2387_);
                    v___x_2396_ = crate::leanh::lean_box(0);
                    v_isShared_2397_ = v_isSharedCheck_2416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2398_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1;
                v___f_2399_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2391_);
                v___f_2400_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2400_, 0, v_toFunctor_2391_);
                v___f_2401_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2401_, 0, v_toFunctor_2391_);
                v___x_2402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2402_, 0, v___f_2400_);
                crate::leanh::lean_ctor_set(v___x_2402_, 1, v___f_2401_);
                v___f_2403_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2403_, 0, v_toSeqRight_2394_);
                v___f_2404_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2404_, 0, v_toSeqLeft_2393_);
                v___f_2405_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2405_, 0, v_toSeq_2392_);
                if v_isShared_2397_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2396_, 4, v___f_2403_);
                    crate::leanh::lean_ctor_set(v___x_2396_, 3, v___f_2404_);
                    crate::leanh::lean_ctor_set(v___x_2396_, 2, v___f_2405_);
                    crate::leanh::lean_ctor_set(v___x_2396_, 1, v___f_2398_);
                    crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2402_);
                    v___x_2407_ = v___x_2396_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2415_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___f_2398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___f_2405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 3, v___f_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 4, v___f_2403_);
                    v___x_2407_ = v_reuseFailAlloc_2415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2389_, 1, v___f_2399_);
                    crate::leanh::lean_ctor_set(v___x_2389_, 0, v___x_2407_);
                    v___x_2409_ = v___x_2389_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___f_2399_);
                    v___x_2409_ = v_reuseFailAlloc_2414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2410_ = crate::leanh::lean_box(0);
                v___x_2411_ = l_instInhabitedOfMonad___redArg(v___x_2409_, v___x_2410_);
                v___x_25987__overap_2412_ = lean_panic_fn_borrowed(v___x_2411_, v_msg_2381_);
                crate::leanh::lean_dec(v___x_2411_);
                crate::leanh::lean_inc(v___y_2383_);
                crate::leanh::lean_inc_ref(v___y_2382_);
                v___x_2413_ = crate::leanh::lean_apply_3(
                    v___x_25987__overap_2412_,
                    v___y_2382_,
                    v___y_2383_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___boxed(
    mut v_msg_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_2420_, v___y_2421_, v___y_2422_);
    crate::leanh::lean_dec(v___y_2422_);
    crate::leanh::lean_dec_ref(v___y_2421_);
    return v_res_2424_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2428_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2;
    v___x_2429_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2430_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_2431_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1;
    v___x_2432_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0;
    v___x_2433_ = l_mkPanicMessageWithDecl(
        v___x_2432_,
        v___x_2431_,
        v___x_2430_,
        v___x_2429_,
        v___x_2428_,
    );
    return v___x_2433_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(
    mut v_preNode_2434_: *mut crate::leanh::LeanObject,
    mut v_postNode_2435_: *mut crate::leanh::LeanObject,
    mut v_x_2436_: *mut crate::leanh::LeanObject,
    mut v_x_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_a_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2472_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v_unused_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_a_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v_a_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2517_: u8 = 0;
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_unused_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2437_) {
                0 => {
                    v_i_2441_ = crate::leanh::lean_ctor_get(v_x_2437_, 0);
                    crate::leanh::lean_inc_ref(v_i_2441_);
                    v_t_2442_ = crate::leanh::lean_ctor_get(v_x_2437_, 1);
                    crate::leanh::lean_inc_ref(v_t_2442_);
                    crate::leanh::lean_dec_ref_known(v_x_2437_, 2);
                    v___x_2443_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2441_, v_x_2436_);
                    v_x_2436_ = v___x_2443_;
                    v_x_2437_ = v_t_2442_;
                    state = 0;
                    continue;
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_2436_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_2437_, 2);
                        crate::leanh::lean_dec_ref(v_postNode_2435_);
                        crate::leanh::lean_dec_ref(v_preNode_2434_);
                        v___x_2445_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3);
                        v___x_2446_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v___x_2445_, v___y_2438_, v___y_2439_);
                        return v___x_2446_;
                    } else {
                        v_i_2447_ = crate::leanh::lean_ctor_get(v_x_2437_, 0);
                        crate::leanh::lean_inc_ref_n(v_i_2447_, 2);
                        v_children_2448_ = crate::leanh::lean_ctor_get(v_x_2437_, 1);
                        crate::leanh::lean_inc_ref_n(v_children_2448_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_2437_, 2);
                        v_val_2449_ = crate::leanh::lean_ctor_get(v_x_2436_, 0);
                        crate::leanh::lean_inc_n(v_val_2449_, 2);
                        crate::leanh::lean_inc_ref(v_preNode_2434_);
                        crate::leanh::lean_inc(v___y_2439_);
                        crate::leanh::lean_inc_ref(v___y_2438_);
                        v___x_2450_ = crate::leanh::lean_apply_6(
                            v_preNode_2434_,
                            v_val_2449_,
                            v_i_2447_,
                            v_children_2448_,
                            v___y_2438_,
                            v___y_2439_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_2450_) == 0 {
                            v_a_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                            crate::leanh::lean_inc(v_a_2451_);
                            crate::leanh::lean_dec_ref_known(v___x_2450_, 1);
                            v___x_2452_ = (crate::leanh::lean_unbox(v_a_2451_) as u8);
                            crate::leanh::lean_dec(v_a_2451_);
                            if v___x_2452_ == 0 {
                                crate::leanh::lean_dec_ref(v_preNode_2434_);
                                v_isSharedCheck_2477_ =
                                    (!crate::leanh::lean_is_exclusive(v_x_2436_)) as u8;
                                if v_isSharedCheck_2477_ == 0 {
                                    v_unused_2478_ = crate::leanh::lean_ctor_get(v_x_2436_, 0);
                                    crate::leanh::lean_dec(v_unused_2478_);
                                    v___x_2454_ = v_x_2436_;
                                    v_isShared_2455_ = v_isSharedCheck_2477_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_x_2436_);
                                    v___x_2454_ = crate::leanh::lean_box(0);
                                    v_isShared_2455_ = v_isSharedCheck_2477_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2479_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_2436_, v_i_2447_);
                                v___x_2480_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_2448_);
                                v___x_2481_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_ref(v_postNode_2435_);
                                v___x_2482_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_2434_, v_postNode_2435_, v___x_2479_, v___x_2480_, v___x_2481_, v___y_2438_, v___y_2439_);
                                if crate::leanh::lean_obj_tag(v___x_2482_) == 0 {
                                    v_a_2483_ = crate::leanh::lean_ctor_get(v___x_2482_, 0);
                                    crate::leanh::lean_inc(v_a_2483_);
                                    crate::leanh::lean_dec_ref_known(v___x_2482_, 1);
                                    crate::leanh::lean_inc(v___y_2439_);
                                    crate::leanh::lean_inc_ref(v___y_2438_);
                                    v___x_2484_ = crate::leanh::lean_apply_7(
                                        v_postNode_2435_,
                                        v_val_2449_,
                                        v_i_2447_,
                                        v_children_2448_,
                                        v_a_2483_,
                                        v___y_2438_,
                                        v___y_2439_,
                                        crate::leanh::lean_box(0),
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2484_) == 0 {
                                        v_a_2485_ = crate::leanh::lean_ctor_get(v___x_2484_, 0);
                                        v_isSharedCheck_2493_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2484_)) as u8;
                                        if v_isSharedCheck_2493_ == 0 {
                                            v___x_2487_ = v___x_2484_;
                                            v_isShared_2488_ = v_isSharedCheck_2493_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2485_);
                                            crate::leanh::lean_dec(v___x_2484_);
                                            v___x_2487_ = crate::leanh::lean_box(0);
                                            v_isShared_2488_ = v_isSharedCheck_2493_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_2494_ = crate::leanh::lean_ctor_get(v___x_2484_, 0);
                                        v_isSharedCheck_2501_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2484_)) as u8;
                                        if v_isSharedCheck_2501_ == 0 {
                                            v___x_2496_ = v___x_2484_;
                                            v_isShared_2497_ = v_isSharedCheck_2501_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2494_);
                                            crate::leanh::lean_dec(v___x_2484_);
                                            v___x_2496_ = crate::leanh::lean_box(0);
                                            v_isShared_2497_ = v_isSharedCheck_2501_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_2449_);
                                    crate::leanh::lean_dec_ref(v_children_2448_);
                                    crate::leanh::lean_dec_ref(v_i_2447_);
                                    crate::leanh::lean_dec_ref(v_postNode_2435_);
                                    v_a_2502_ = crate::leanh::lean_ctor_get(v___x_2482_, 0);
                                    v_isSharedCheck_2509_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2482_)) as u8;
                                    if v_isSharedCheck_2509_ == 0 {
                                        v___x_2504_ = v___x_2482_;
                                        v_isShared_2505_ = v_isSharedCheck_2509_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2502_);
                                        crate::leanh::lean_dec(v___x_2482_);
                                        v___x_2504_ = crate::leanh::lean_box(0);
                                        v_isShared_2505_ = v_isSharedCheck_2509_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_2449_);
                            crate::leanh::lean_dec_ref(v_children_2448_);
                            crate::leanh::lean_dec_ref(v_i_2447_);
                            crate::leanh::lean_dec_ref_known(v_x_2436_, 1);
                            crate::leanh::lean_dec_ref(v_postNode_2435_);
                            crate::leanh::lean_dec_ref(v_preNode_2434_);
                            v_a_2510_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                            v_isSharedCheck_2517_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2450_)) as u8;
                            if v_isSharedCheck_2517_ == 0 {
                                v___x_2512_ = v___x_2450_;
                                v_isShared_2513_ = v_isSharedCheck_2517_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2510_);
                                crate::leanh::lean_dec(v___x_2450_);
                                v___x_2512_ = crate::leanh::lean_box(0);
                                v_isShared_2513_ = v_isSharedCheck_2517_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_2436_);
                    crate::leanh::lean_dec_ref(v_postNode_2435_);
                    crate::leanh::lean_dec_ref(v_preNode_2434_);
                    v_isSharedCheck_2525_ = (!crate::leanh::lean_is_exclusive(v_x_2437_)) as u8;
                    if v_isSharedCheck_2525_ == 0 {
                        v_unused_2526_ = crate::leanh::lean_ctor_get(v_x_2437_, 0);
                        crate::leanh::lean_dec(v_unused_2526_);
                        v___x_2519_ = v_x_2437_;
                        v_isShared_2520_ = v_isSharedCheck_2525_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2437_);
                        v___x_2519_ = crate::leanh::lean_box(0);
                        v_isShared_2520_ = v_isSharedCheck_2525_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2456_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2439_);
                crate::leanh::lean_inc_ref(v___y_2438_);
                v___x_2457_ = crate::leanh::lean_apply_7(
                    v_postNode_2435_,
                    v_val_2449_,
                    v_i_2447_,
                    v_children_2448_,
                    v___x_2456_,
                    v___y_2438_,
                    v___y_2439_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                    v_a_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                    v_isSharedCheck_2468_ = (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2460_ = v___x_2457_;
                        v_isShared_2461_ = v_isSharedCheck_2468_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2458_);
                        crate::leanh::lean_dec(v___x_2457_);
                        v___x_2460_ = crate::leanh::lean_box(0);
                        v_isShared_2461_ = v_isSharedCheck_2468_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2454_);
                    v_a_2469_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                    v_isSharedCheck_2476_ = (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2471_ = v___x_2457_;
                        v_isShared_2472_ = v_isSharedCheck_2476_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2469_);
                        crate::leanh::lean_dec(v___x_2457_);
                        v___x_2471_ = crate::leanh::lean_box(0);
                        v_isShared_2472_ = v_isSharedCheck_2476_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2454_, 0, v_a_2458_);
                    v___x_2463_ = v___x_2454_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2458_);
                    v___x_2463_ = v_reuseFailAlloc_2467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2460_, 0, v___x_2463_);
                    v___x_2465_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2465_;
            }
            5 => {
                if v_isShared_2472_ == 0 {
                    v___x_2474_ = v___x_2471_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2474_;
            }
            7 => {
                v___x_2489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2489_, 0, v_a_2485_);
                if v_isShared_2488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2487_, 0, v___x_2489_);
                    v___x_2491_ = v___x_2487_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
                    v___x_2491_ = v_reuseFailAlloc_2492_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2491_;
            }
            9 => {
                if v_isShared_2497_ == 0 {
                    v___x_2499_ = v___x_2496_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2499_;
            }
            11 => {
                if v_isShared_2505_ == 0 {
                    v___x_2507_ = v___x_2504_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2507_;
            }
            13 => {
                if v_isShared_2513_ == 0 {
                    v___x_2515_ = v___x_2512_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
                    v___x_2515_ = v_reuseFailAlloc_2516_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2515_;
            }
            15 => {
                v___x_2521_ = crate::leanh::lean_box(0);
                if v_isShared_2520_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2519_, 0);
                    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2521_);
                    v___x_2523_ = v___x_2519_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
                    v___x_2523_ = v_reuseFailAlloc_2524_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(
    mut v_preNode_2527_: *mut crate::leanh::LeanObject,
    mut v_postNode_2528_: *mut crate::leanh::LeanObject,
    mut v___x_2529_: *mut crate::leanh::LeanObject,
    mut v_x_2530_: *mut crate::leanh::LeanObject,
    mut v_x_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2530_) == 0 {
                    crate::leanh::lean_dec(v___x_2529_);
                    crate::leanh::lean_dec_ref(v_postNode_2528_);
                    crate::leanh::lean_dec_ref(v_preNode_2527_);
                    v___x_2535_ = l_List_reverse___redArg(v_x_2531_);
                    v___x_2536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2536_, 0, v___x_2535_);
                    return v___x_2536_;
                } else {
                    v_head_2537_ = crate::leanh::lean_ctor_get(v_x_2530_, 0);
                    v_tail_2538_ = crate::leanh::lean_ctor_get(v_x_2530_, 1);
                    v_isSharedCheck_2556_ = (!crate::leanh::lean_is_exclusive(v_x_2530_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2540_ = v_x_2530_;
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2538_);
                        crate::leanh::lean_inc(v_head_2537_);
                        crate::leanh::lean_dec(v_x_2530_);
                        v___x_2540_ = crate::leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_2529_);
                crate::leanh::lean_inc_ref(v_postNode_2528_);
                crate::leanh::lean_inc_ref(v_preNode_2527_);
                v___x_2542_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2527_, v_postNode_2528_, v___x_2529_, v_head_2537_, v___y_2532_, v___y_2533_);
                if crate::leanh::lean_obj_tag(v___x_2542_) == 0 {
                    v_a_2543_ = crate::leanh::lean_ctor_get(v___x_2542_, 0);
                    crate::leanh::lean_inc(v_a_2543_);
                    crate::leanh::lean_dec_ref_known(v___x_2542_, 1);
                    if v_isShared_2541_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2540_, 1, v_x_2531_);
                        crate::leanh::lean_ctor_set(v___x_2540_, 0, v_a_2543_);
                        v___x_2545_ = v___x_2540_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2547_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2543_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_x_2531_);
                        v___x_2545_ = v_reuseFailAlloc_2547_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2540_);
                    crate::leanh::lean_dec(v_tail_2538_);
                    crate::leanh::lean_dec(v_x_2531_);
                    crate::leanh::lean_dec(v___x_2529_);
                    crate::leanh::lean_dec_ref(v_postNode_2528_);
                    crate::leanh::lean_dec_ref(v_preNode_2527_);
                    v_a_2548_ = crate::leanh::lean_ctor_get(v___x_2542_, 0);
                    v_isSharedCheck_2555_ = (!crate::leanh::lean_is_exclusive(v___x_2542_)) as u8;
                    if v_isSharedCheck_2555_ == 0 {
                        v___x_2550_ = v___x_2542_;
                        v_isShared_2551_ = v_isSharedCheck_2555_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2548_);
                        crate::leanh::lean_dec(v___x_2542_);
                        v___x_2550_ = crate::leanh::lean_box(0);
                        v_isShared_2551_ = v_isSharedCheck_2555_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_2530_ = v_tail_2538_;
                v_x_2531_ = v___x_2545_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2551_ == 0 {
                    v___x_2553_ = v___x_2550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
                    v___x_2553_ = v_reuseFailAlloc_2554_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg___boxed(
    mut v_preNode_2557_: *mut crate::leanh::LeanObject,
    mut v_postNode_2558_: *mut crate::leanh::LeanObject,
    mut v___x_2559_: *mut crate::leanh::LeanObject,
    mut v_x_2560_: *mut crate::leanh::LeanObject,
    mut v_x_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2565_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_2557_, v_postNode_2558_, v___x_2559_, v_x_2560_, v_x_2561_, v___y_2562_, v___y_2563_);
    crate::leanh::lean_dec(v___y_2563_);
    crate::leanh::lean_dec_ref(v___y_2562_);
    return v_res_2565_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___boxed(
    mut v_preNode_2566_: *mut crate::leanh::LeanObject,
    mut v_postNode_2567_: *mut crate::leanh::LeanObject,
    mut v_x_2568_: *mut crate::leanh::LeanObject,
    mut v_x_2569_: *mut crate::leanh::LeanObject,
    mut v___y_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2573_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2566_, v_postNode_2567_, v_x_2568_, v_x_2569_, v___y_2570_, v___y_2571_);
    crate::leanh::lean_dec(v___y_2571_);
    crate::leanh::lean_dec_ref(v___y_2570_);
    return v_res_2573_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(
    mut v_preNode_2574_: *mut crate::leanh::LeanObject,
    mut v_postNode_2575_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2576_: *mut crate::leanh::LeanObject,
    mut v_t_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_unused_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2581_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2581_, 0, v_postNode_2575_);
                v___x_2582_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2574_, v___f_2581_, v_ctx_x3f_2576_, v_t_2577_, v___y_2578_, v___y_2579_);
                if crate::leanh::lean_obj_tag(v___x_2582_) == 0 {
                    v_isSharedCheck_2590_ = (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v_unused_2591_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                        crate::leanh::lean_dec(v_unused_2591_);
                        v___x_2584_ = v___x_2582_;
                        v_isShared_2585_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2582_);
                        v___x_2584_ = crate::leanh::lean_box(0);
                        v_isShared_2585_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2592_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                    v_isSharedCheck_2599_ = (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2599_ == 0 {
                        v___x_2594_ = v___x_2582_;
                        v_isShared_2595_ = v_isSharedCheck_2599_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2592_);
                        crate::leanh::lean_dec(v___x_2582_);
                        v___x_2594_ = crate::leanh::lean_box(0);
                        v_isShared_2595_ = v_isSharedCheck_2599_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2586_ = crate::leanh::lean_box(0);
                if v_isShared_2585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2586_);
                    v___x_2588_ = v___x_2584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2588_;
            }
            3 => {
                if v_isShared_2595_ == 0 {
                    v___x_2597_ = v___x_2594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(
    mut v_preNode_2600_: *mut crate::leanh::LeanObject,
    mut v_postNode_2601_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2602_: *mut crate::leanh::LeanObject,
    mut v_t_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_preNode_2600_, v_postNode_2601_, v_ctx_x3f_2602_, v_t_2603_, v___y_2604_, v___y_2605_);
    crate::leanh::lean_dec(v___y_2605_);
    crate::leanh::lean_dec_ref(v___y_2604_);
    return v_res_2607_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(
    mut v___y_2609_: u8,
    mut v_suppressElabErrors_2610_: u8,
    mut v_x_2611_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2611_) == 1 {
        let mut v_pre_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2612_ = crate::leanh::lean_ctor_get(v_x_2611_, 0);
        if crate::leanh::lean_obj_tag(v_pre_2612_) == 0 {
            let mut v_str_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2615_: u8 = 0;
            v_str_2613_ = crate::leanh::lean_ctor_get(v_x_2611_, 1);
            v___x_2614_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0;
            v___x_2615_ = lean_string_dec_eq(v_str_2613_, v___x_2614_);
            if v___x_2615_ == 0 {
                return v___y_2609_;
            } else {
                return v_suppressElabErrors_2610_;
            }
        } else {
            return v___y_2609_;
        }
    } else {
        return v___y_2609_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed(
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2617_: *mut crate::leanh::LeanObject,
    mut v_x_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_29418__boxed_2619_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2620_: u8 = 0;
    let mut v_res_2621_: u8 = 0;
    let mut v_r_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_29418__boxed_2619_ = (crate::leanh::lean_unbox(v___y_2616_) as u8);
    v_suppressElabErrors_boxed_2620_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2617_) as u8);
    v_res_2621_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(v___y_29418__boxed_2619_, v_suppressElabErrors_boxed_2620_, v_x_2618_);
    crate::leanh::lean_dec(v_x_2618_);
    v_r_2622_ = crate::leanh::lean_box((v_res_2621_) as usize);
    return v_r_2622_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2623_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0);
    v___x_2625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2625_, 0, v___x_2624_);
    return v___x_2625_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
    v___x_2627_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2628_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2628_, 0, v___x_2627_);
    crate::leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
    crate::leanh::lean_ctor_set(v___x_2628_, 2, v___x_2627_);
    crate::leanh::lean_ctor_set(v___x_2628_, 3, v___x_2627_);
    crate::leanh::lean_ctor_set(v___x_2628_, 4, v___x_2626_);
    crate::leanh::lean_ctor_set(v___x_2628_, 5, v___x_2626_);
    crate::leanh::lean_ctor_set(v___x_2628_, 6, v___x_2626_);
    crate::leanh::lean_ctor_set(v___x_2628_, 7, v___x_2626_);
    crate::leanh::lean_ctor_set(v___x_2628_, 8, v___x_2626_);
    crate::leanh::lean_ctor_set(v___x_2628_, 9, v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
    v___x_2631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2631_, 0, v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: usize = 0;
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = 5usize;
    v___x_2633_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2634_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2635_ = lean_mk_empty_array_with_capacity(v___x_2634_);
    v___x_2636_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3);
    v___x_2637_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2637_, 0, v___x_2636_);
    crate::leanh::lean_ctor_set(v___x_2637_, 1, v___x_2635_);
    crate::leanh::lean_ctor_set(v___x_2637_, 2, v___x_2633_);
    crate::leanh::lean_ctor_set(v___x_2637_, 3, v___x_2633_);
    crate::leanh::lean_ctor_set_usize(v___x_2637_, 4, v___x_2632_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = crate::leanh::lean_box(1);
    v___x_2639_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
    v___x_2640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
    v___x_2641_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
    crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2639_);
    crate::leanh::lean_ctor_set(v___x_2641_, 2, v___x_2638_);
    return v___x_2641_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(
    mut v_msgData_2642_: *mut crate::leanh::LeanObject,
    mut v___y_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = lean_st_ref_get(v___y_2643_);
    v_env_2646_ = crate::leanh::lean_ctor_get(v___x_2645_, 0);
    crate::leanh::lean_inc_ref(v_env_2646_);
    crate::leanh::lean_dec(v___x_2645_);
    v___x_2647_ = lean_st_ref_get(v___y_2643_);
    v_scopes_2648_ = crate::leanh::lean_ctor_get(v___x_2647_, 2);
    crate::leanh::lean_inc(v_scopes_2648_);
    crate::leanh::lean_dec(v___x_2647_);
    v___x_2649_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2650_ = l_List_head_x21___redArg(v___x_2649_, v_scopes_2648_);
    crate::leanh::lean_dec(v_scopes_2648_);
    v_opts_2651_ = crate::leanh::lean_ctor_get(v___x_2650_, 1);
    crate::leanh::lean_inc_ref(v_opts_2651_);
    crate::leanh::lean_dec(v___x_2650_);
    v___x_2652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2);
    v___x_2653_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5);
    v___x_2654_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2654_, 0, v_env_2646_);
    crate::leanh::lean_ctor_set(v___x_2654_, 1, v___x_2652_);
    crate::leanh::lean_ctor_set(v___x_2654_, 2, v___x_2653_);
    crate::leanh::lean_ctor_set(v___x_2654_, 3, v_opts_2651_);
    v___x_2655_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2655_, 0, v___x_2654_);
    crate::leanh::lean_ctor_set(v___x_2655_, 1, v_msgData_2642_);
    v___x_2656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2655_);
    return v___x_2656_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___boxed(
    mut v_msgData_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2660_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_2657_, v___y_2658_);
    crate::leanh::lean_dec(v___y_2658_);
    return v_res_2660_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(
    mut v_ref_2662_: *mut crate::leanh::LeanObject,
    mut v_msgData_2663_: *mut crate::leanh::LeanObject,
    mut v_severity_2664_: u8,
    mut v_isSilent_2665_: u8,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
    mut v___y_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: u8 = 0;
    let mut v___y_2674_: u8 = 0;
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_a_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v___y_2733_: u8 = 0;
    let mut v___y_2734_: u8 = 0;
    let mut v___y_2735_: u8 = 0;
    let mut v___y_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v___y_2761_: u8 = 0;
    let mut v___y_2762_: u8 = 0;
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: u8 = 0;
    let mut v___y_2770_: u8 = 0;
    let mut v___y_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v___x_2786_: u8 = 0;
    let mut v___y_2788_: u8 = 0;
    let mut v___y_2789_: u8 = 0;
    let mut v___y_2790_: u8 = 0;
    let mut v___y_2792_: u8 = 0;
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2786_ = 2;
                v___x_2804_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2664_, v___x_2786_);
                if v___x_2804_ == 0 {
                    v___y_2792_ = v___x_2804_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2663_);
                    v___x_2805_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2663_);
                    v___y_2792_ = v___x_2805_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2678_ = l_Lean_Elab_Command_getScope___redArg(v___y_2677_);
                if crate::leanh::lean_obj_tag(v___x_2678_) == 0 {
                    v_a_2679_ = crate::leanh::lean_ctor_get(v___x_2678_, 0);
                    crate::leanh::lean_inc(v_a_2679_);
                    crate::leanh::lean_dec_ref_known(v___x_2678_, 1);
                    v___x_2680_ = l_Lean_Elab_Command_getScope___redArg(v___y_2677_);
                    if crate::leanh::lean_obj_tag(v___x_2680_) == 0 {
                        v_a_2681_ = crate::leanh::lean_ctor_get(v___x_2680_, 0);
                        v_isSharedCheck_2715_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2680_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2683_ = v___x_2680_;
                            v_isShared_2684_ = v_isSharedCheck_2715_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2681_);
                            crate::leanh::lean_dec(v___x_2680_);
                            v___x_2683_ = crate::leanh::lean_box(0);
                            v_isShared_2684_ = v_isSharedCheck_2715_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2679_);
                        crate::leanh::lean_dec_ref(v___y_2675_);
                        crate::leanh::lean_dec(v___y_2672_);
                        crate::leanh::lean_dec_ref(v___y_2670_);
                        v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2680_, 0);
                        v_isSharedCheck_2723_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2680_)) as u8;
                        if v_isSharedCheck_2723_ == 0 {
                            v___x_2718_ = v___x_2680_;
                            v_isShared_2719_ = v_isSharedCheck_2723_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2716_);
                            crate::leanh::lean_dec(v___x_2680_);
                            v___x_2718_ = crate::leanh::lean_box(0);
                            v_isShared_2719_ = v_isSharedCheck_2723_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2675_);
                    crate::leanh::lean_dec(v___y_2672_);
                    crate::leanh::lean_dec_ref(v___y_2670_);
                    v_a_2724_ = crate::leanh::lean_ctor_get(v___x_2678_, 0);
                    v_isSharedCheck_2731_ = (!crate::leanh::lean_is_exclusive(v___x_2678_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2726_ = v___x_2678_;
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2724_);
                        crate::leanh::lean_dec(v___x_2678_);
                        v___x_2726_ = crate::leanh::lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = lean_st_ref_take(v___y_2677_);
                v_currNamespace_2686_ = crate::leanh::lean_ctor_get(v_a_2679_, 2);
                crate::leanh::lean_inc(v_currNamespace_2686_);
                crate::leanh::lean_dec(v_a_2679_);
                v_openDecls_2687_ = crate::leanh::lean_ctor_get(v_a_2681_, 3);
                crate::leanh::lean_inc(v_openDecls_2687_);
                crate::leanh::lean_dec(v_a_2681_);
                v_env_2688_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                v_messages_2689_ = crate::leanh::lean_ctor_get(v___x_2685_, 1);
                v_scopes_2690_ = crate::leanh::lean_ctor_get(v___x_2685_, 2);
                v_usedQuotCtxts_2691_ = crate::leanh::lean_ctor_get(v___x_2685_, 3);
                v_nextMacroScope_2692_ = crate::leanh::lean_ctor_get(v___x_2685_, 4);
                v_maxRecDepth_2693_ = crate::leanh::lean_ctor_get(v___x_2685_, 5);
                v_ngen_2694_ = crate::leanh::lean_ctor_get(v___x_2685_, 6);
                v_auxDeclNGen_2695_ = crate::leanh::lean_ctor_get(v___x_2685_, 7);
                v_infoState_2696_ = crate::leanh::lean_ctor_get(v___x_2685_, 8);
                v_traceState_2697_ = crate::leanh::lean_ctor_get(v___x_2685_, 9);
                v_snapshotTasks_2698_ = crate::leanh::lean_ctor_get(v___x_2685_, 10);
                v_isSharedCheck_2714_ = (!crate::leanh::lean_is_exclusive(v___x_2685_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2700_ = v___x_2685_;
                    v_isShared_2701_ = v_isSharedCheck_2714_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2698_);
                    crate::leanh::lean_inc(v_traceState_2697_);
                    crate::leanh::lean_inc(v_infoState_2696_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2695_);
                    crate::leanh::lean_inc(v_ngen_2694_);
                    crate::leanh::lean_inc(v_maxRecDepth_2693_);
                    crate::leanh::lean_inc(v_nextMacroScope_2692_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2691_);
                    crate::leanh::lean_inc(v_scopes_2690_);
                    crate::leanh::lean_inc(v_messages_2689_);
                    crate::leanh::lean_inc(v_env_2688_);
                    crate::leanh::lean_dec(v___x_2685_);
                    v___x_2700_ = crate::leanh::lean_box(0);
                    v_isShared_2701_ = v_isSharedCheck_2714_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2702_, 0, v_currNamespace_2686_);
                crate::leanh::lean_ctor_set(v___x_2702_, 1, v_openDecls_2687_);
                v___x_2703_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
                crate::leanh::lean_ctor_set(v___x_2703_, 1, v___y_2675_);
                crate::leanh::lean_inc_ref(v___y_2671_);
                crate::leanh::lean_inc_ref(v___y_2676_);
                v___x_2704_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2704_, 0, v___y_2676_);
                crate::leanh::lean_ctor_set(v___x_2704_, 1, v___y_2670_);
                crate::leanh::lean_ctor_set(v___x_2704_, 2, v___y_2672_);
                crate::leanh::lean_ctor_set(v___x_2704_, 3, v___y_2671_);
                crate::leanh::lean_ctor_set(v___x_2704_, 4, v___x_2703_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2674_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2673_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2665_,
                );
                v___x_2705_ = l_Lean_MessageLog_add(v___x_2704_, v_messages_2689_);
                if v_isShared_2701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2700_, 1, v___x_2705_);
                    v___x_2707_ = v___x_2700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_env_2688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 2, v_scopes_2690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 3, v_usedQuotCtxts_2691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_nextMacroScope_2692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 5, v_maxRecDepth_2693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 6, v_ngen_2694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 7, v_auxDeclNGen_2695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 8, v_infoState_2696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 9, v_traceState_2697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 10, v_snapshotTasks_2698_);
                    v___x_2707_ = v_reuseFailAlloc_2713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2708_ = lean_st_ref_set(v___y_2677_, v___x_2707_);
                v___x_2709_ = crate::leanh::lean_box(0);
                if v_isShared_2684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2683_, 0, v___x_2709_);
                    v___x_2711_ = v___x_2683_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2711_;
            }
            6 => {
                if v_isShared_2719_ == 0 {
                    v___x_2721_ = v___x_2718_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
                    v___x_2721_ = v_reuseFailAlloc_2722_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2721_;
            }
            8 => {
                if v_isShared_2727_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2729_;
            }
            10 => {
                v_fileName_2738_ = crate::leanh::lean_ctor_get(v___y_2666_, 0);
                v_fileMap_2739_ = crate::leanh::lean_ctor_get(v___y_2666_, 1);
                v_suppressElabErrors_2740_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2666_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_2741_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2663_,
                    );
                v___x_2742_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v___x_2741_, v___y_2667_);
                v_a_2743_ = crate::leanh::lean_ctor_get(v___x_2742_, 0);
                v_isSharedCheck_2759_ = (!crate::leanh::lean_is_exclusive(v___x_2742_)) as u8;
                if v_isSharedCheck_2759_ == 0 {
                    v___x_2745_ = v___x_2742_;
                    v_isShared_2746_ = v_isSharedCheck_2759_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2743_);
                    crate::leanh::lean_dec(v___x_2742_);
                    v___x_2745_ = crate::leanh::lean_box(0);
                    v_isShared_2746_ = v_isSharedCheck_2759_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_2739_, 2);
                v___x_2747_ = l_Lean_FileMap_toPosition(v_fileMap_2739_, v___y_2736_);
                crate::leanh::lean_dec(v___y_2736_);
                v___x_2748_ = l_Lean_FileMap_toPosition(v_fileMap_2739_, v___y_2737_);
                crate::leanh::lean_dec(v___y_2737_);
                v___x_2749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
                v___x_2750_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0;
                if v_suppressElabErrors_2740_ == 0 {
                    crate::leanh::lean_del_object(v___x_2745_);
                    v___y_2670_ = v___x_2747_;
                    v___y_2671_ = v___x_2750_;
                    v___y_2672_ = v___x_2749_;
                    v___y_2673_ = v___y_2734_;
                    v___y_2674_ = v___y_2735_;
                    v___y_2675_ = v_a_2743_;
                    v___y_2676_ = v_fileName_2738_;
                    v___y_2677_ = v___y_2667_;
                    state = 1;
                    continue;
                } else {
                    v___x_2751_ = crate::leanh::lean_box((v___y_2733_) as usize);
                    v___x_2752_ = crate::leanh::lean_box((v_suppressElabErrors_2740_) as usize);
                    v___f_2753_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2753_, 0, v___x_2751_);
                    crate::leanh::lean_closure_set(v___f_2753_, 1, v___x_2752_);
                    crate::leanh::lean_inc(v_a_2743_);
                    v___x_2754_ = l_Lean_MessageData_hasTag(v___f_2753_, v_a_2743_);
                    if v___x_2754_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2749_, 1);
                        crate::leanh::lean_dec_ref(v___x_2747_);
                        crate::leanh::lean_dec(v_a_2743_);
                        v___x_2755_ = crate::leanh::lean_box(0);
                        if v_isShared_2746_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2745_, 0, v___x_2755_);
                            v___x_2757_ = v___x_2745_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2758_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
                            v___x_2757_ = v_reuseFailAlloc_2758_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2745_);
                        v___y_2670_ = v___x_2747_;
                        v___y_2671_ = v___x_2750_;
                        v___y_2672_ = v___x_2749_;
                        v___y_2673_ = v___y_2734_;
                        v___y_2674_ = v___y_2735_;
                        v___y_2675_ = v_a_2743_;
                        v___y_2676_ = v_fileName_2738_;
                        v___y_2677_ = v___y_2667_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_2757_;
            }
            13 => {
                v___x_2766_ = l_Lean_Syntax_getTailPos_x3f(v___y_2764_, v___y_2763_);
                crate::leanh::lean_dec(v___y_2764_);
                if crate::leanh::lean_obj_tag(v___x_2766_) == 0 {
                    crate::leanh::lean_inc(v___y_2765_);
                    v___y_2733_ = v___y_2761_;
                    v___y_2734_ = v___y_2762_;
                    v___y_2735_ = v___y_2763_;
                    v___y_2736_ = v___y_2765_;
                    v___y_2737_ = v___y_2765_;
                    state = 10;
                    continue;
                } else {
                    v_val_2767_ = crate::leanh::lean_ctor_get(v___x_2766_, 0);
                    crate::leanh::lean_inc(v_val_2767_);
                    crate::leanh::lean_dec_ref_known(v___x_2766_, 1);
                    v___y_2733_ = v___y_2761_;
                    v___y_2734_ = v___y_2762_;
                    v___y_2735_ = v___y_2763_;
                    v___y_2736_ = v___y_2765_;
                    v___y_2737_ = v_val_2767_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_2772_ = l_Lean_Elab_Command_getRef___redArg(v___y_2666_);
                if crate::leanh::lean_obj_tag(v___x_2772_) == 0 {
                    v_a_2773_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                    crate::leanh::lean_inc(v_a_2773_);
                    crate::leanh::lean_dec_ref_known(v___x_2772_, 1);
                    v_ref_2774_ = l_Lean_replaceRef(v_ref_2662_, v_a_2773_);
                    crate::leanh::lean_dec(v_a_2773_);
                    v___x_2775_ = l_Lean_Syntax_getPos_x3f(v_ref_2774_, v___y_2770_);
                    if crate::leanh::lean_obj_tag(v___x_2775_) == 0 {
                        v___x_2776_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_2761_ = v___y_2769_;
                        v___y_2762_ = v___y_2771_;
                        v___y_2763_ = v___y_2770_;
                        v___y_2764_ = v_ref_2774_;
                        v___y_2765_ = v___x_2776_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2777_ = crate::leanh::lean_ctor_get(v___x_2775_, 0);
                        crate::leanh::lean_inc(v_val_2777_);
                        crate::leanh::lean_dec_ref_known(v___x_2775_, 1);
                        v___y_2761_ = v___y_2769_;
                        v___y_2762_ = v___y_2771_;
                        v___y_2763_ = v___y_2770_;
                        v___y_2764_ = v_ref_2774_;
                        v___y_2765_ = v_val_2777_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2663_);
                    v_a_2778_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                    v_isSharedCheck_2785_ = (!crate::leanh::lean_is_exclusive(v___x_2772_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2780_ = v___x_2772_;
                        v_isShared_2781_ = v_isSharedCheck_2785_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2778_);
                        crate::leanh::lean_dec(v___x_2772_);
                        v___x_2780_ = crate::leanh::lean_box(0);
                        v_isShared_2781_ = v_isSharedCheck_2785_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2781_ == 0 {
                    v___x_2783_ = v___x_2780_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
                    v___x_2783_ = v_reuseFailAlloc_2784_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2783_;
            }
            17 => {
                if v___y_2790_ == 0 {
                    v___y_2769_ = v___y_2788_;
                    v___y_2770_ = v___y_2789_;
                    v___y_2771_ = v_severity_2664_;
                    state = 14;
                    continue;
                } else {
                    v___y_2769_ = v___y_2788_;
                    v___y_2770_ = v___y_2789_;
                    v___y_2771_ = v___x_2786_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_2792_ == 0 {
                    v___x_2793_ = lean_st_ref_get(v___y_2667_);
                    v_scopes_2794_ = crate::leanh::lean_ctor_get(v___x_2793_, 2);
                    crate::leanh::lean_inc(v_scopes_2794_);
                    crate::leanh::lean_dec(v___x_2793_);
                    v___x_2795_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2796_ = l_List_head_x21___redArg(v___x_2795_, v_scopes_2794_);
                    crate::leanh::lean_dec(v_scopes_2794_);
                    v_opts_2797_ = crate::leanh::lean_ctor_get(v___x_2796_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2797_);
                    crate::leanh::lean_dec(v___x_2796_);
                    v___x_2798_ = 1;
                    v___x_2799_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2664_, v___x_2798_);
                    if v___x_2799_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2797_);
                        v___y_2788_ = v___y_2792_;
                        v___y_2789_ = v___y_2792_;
                        v___y_2790_ = v___x_2799_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2800_ = l_Lean_warningAsError;
                        v___x_2801_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2797_, v___x_2800_);
                        crate::leanh::lean_dec_ref(v_opts_2797_);
                        v___y_2788_ = v___y_2792_;
                        v___y_2789_ = v___y_2792_;
                        v___y_2790_ = v___x_2801_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2663_);
                    v___x_2802_ = crate::leanh::lean_box(0);
                    v___x_2803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2802_);
                    return v___x_2803_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___boxed(
    mut v_ref_2806_: *mut crate::leanh::LeanObject,
    mut v_msgData_2807_: *mut crate::leanh::LeanObject,
    mut v_severity_2808_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2813_: u8 = 0;
    let mut v_isSilent_boxed_2814_: u8 = 0;
    let mut v_res_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2813_ = (crate::leanh::lean_unbox(v_severity_2808_) as u8);
    v_isSilent_boxed_2814_ = (crate::leanh::lean_unbox(v_isSilent_2809_) as u8);
    v_res_2815_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_2806_, v_msgData_2807_, v_severity_boxed_2813_, v_isSilent_boxed_2814_, v___y_2810_, v___y_2811_);
    crate::leanh::lean_dec(v___y_2811_);
    crate::leanh::lean_dec_ref(v___y_2810_);
    crate::leanh::lean_dec(v_ref_2806_);
    return v_res_2815_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(
    mut v_ref_2816_: *mut crate::leanh::LeanObject,
    mut v_msgData_2817_: *mut crate::leanh::LeanObject,
    mut v___y_2818_: *mut crate::leanh::LeanObject,
    mut v___y_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = 1;
    v___x_2822_ = 0;
    v___x_2823_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_2816_, v_msgData_2817_, v___x_2821_, v___x_2822_, v___y_2818_, v___y_2819_);
    return v___x_2823_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15___boxed(
    mut v_ref_2824_: *mut crate::leanh::LeanObject,
    mut v_msgData_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_ref_2824_, v_msgData_2825_, v___y_2826_, v___y_2827_);
    crate::leanh::lean_dec(v___y_2827_);
    crate::leanh::lean_dec_ref(v___y_2826_);
    crate::leanh::lean_dec(v_ref_2824_);
    return v_res_2829_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0;
    v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
    return v___x_2832_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2;
    v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
    return v___x_2835_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(
    mut v_linterOption_2836_: *mut crate::leanh::LeanObject,
    mut v_stx_2837_: *mut crate::leanh::LeanObject,
    mut v_msg_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_unused_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2842_ = crate::leanh::lean_ctor_get(v_linterOption_2836_, 0);
                v_isSharedCheck_2859_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_2836_)) as u8;
                if v_isSharedCheck_2859_ == 0 {
                    v_unused_2860_ = crate::leanh::lean_ctor_get(v_linterOption_2836_, 1);
                    crate::leanh::lean_dec(v_unused_2860_);
                    v___x_2844_ = v_linterOption_2836_;
                    v_isShared_2845_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2842_);
                    crate::leanh::lean_dec(v_linterOption_2836_);
                    v___x_2844_ = crate::leanh::lean_box(0);
                    v_isShared_2845_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2846_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1);
                crate::leanh::lean_inc(v_name_2842_);
                v___x_2847_ = l_Lean_MessageData_ofName(v_name_2842_);
                if v_isShared_2845_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2844_, 7);
                    crate::leanh::lean_ctor_set(v___x_2844_, 1, v___x_2847_);
                    crate::leanh::lean_ctor_set(v___x_2844_, 0, v___x_2846_);
                    v___x_2849_ = v___x_2844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2847_);
                    v___x_2849_ = v_reuseFailAlloc_2858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2850_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3);
                v___x_2851_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2851_, 0, v___x_2849_);
                crate::leanh::lean_ctor_set(v___x_2851_, 1, v___x_2850_);
                v_disable_2852_ = l_Lean_MessageData_note(v___x_2851_);
                v___x_2853_ = l_Lean_Linter_linterMessageTag;
                v___x_2854_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2854_, 0, v_msg_2838_);
                crate::leanh::lean_ctor_set(v___x_2854_, 1, v_disable_2852_);
                v___x_2855_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2853_);
                crate::leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
                v___x_2856_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2856_, 0, v_name_2842_);
                crate::leanh::lean_ctor_set(v___x_2856_, 1, v___x_2855_);
                v___x_2857_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_stx_2837_, v___x_2856_, v___y_2839_, v___y_2840_);
                return v___x_2857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(
    mut v_linterOption_2861_: *mut crate::leanh::LeanObject,
    mut v_stx_2862_: *mut crate::leanh::LeanObject,
    mut v_msg_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2867_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_linterOption_2861_, v_stx_2862_, v_msg_2863_, v___y_2864_, v___y_2865_);
    crate::leanh::lean_dec(v___y_2865_);
    crate::leanh::lean_dec_ref(v___y_2864_);
    crate::leanh::lean_dec(v_stx_2862_);
    return v_res_2867_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2868_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0);
    v___x_2870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    return v___x_2870_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = crate::leanh::lean_box(1);
    v___x_2872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
    v___x_2873_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1);
    v___x_2874_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
    crate::leanh::lean_ctor_set(v___x_2874_, 1, v___x_2872_);
    crate::leanh::lean_ctor_set(v___x_2874_, 2, v___x_2871_);
    return v___x_2874_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(
    mut v_val_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: u8,
    mut v___x_2879_: *mut crate::leanh::LeanObject,
    mut v___f_2880_: *mut crate::leanh::LeanObject,
    mut v_ci_2881_: *mut crate::leanh::LeanObject,
    mut v_info_2882_: *mut crate::leanh::LeanObject,
    mut v_x_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v_toCommandContextInfo_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v_parentDecl_x3f_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2898_: u8 = 0;
    let mut v_env_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_toElabInfo_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctxBefore_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctxAfter_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v_val_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2929_: u8 = 0;
    let mut v_a_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v_ref_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_unused_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_unused_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2887_ = lean_st_ref_get(v_val_2877_);
                v___x_2888_ = (crate::leanh::lean_unbox(v___x_2887_) as u8);
                crate::leanh::lean_dec(v___x_2887_);
                if v___x_2888_ == 0 {
                    if crate::leanh::lean_obj_tag(v_info_2882_) == 0 {
                        v_toCommandContextInfo_2889_ = crate::leanh::lean_ctor_get(v_ci_2881_, 0);
                        crate::leanh::lean_inc_ref(v_toCommandContextInfo_2889_);
                        v_i_2890_ = crate::leanh::lean_ctor_get(v_info_2882_, 0);
                        v_isSharedCheck_2965_ =
                            (!crate::leanh::lean_is_exclusive(v_info_2882_)) as u8;
                        if v_isSharedCheck_2965_ == 0 {
                            v___x_2892_ = v_info_2882_;
                            v_isShared_2893_ = v_isSharedCheck_2965_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_i_2890_);
                            crate::leanh::lean_dec(v_info_2882_);
                            v___x_2892_ = crate::leanh::lean_box(0);
                            v_isShared_2893_ = v_isSharedCheck_2965_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_info_2882_);
                        crate::leanh::lean_dec_ref(v_ci_2881_);
                        crate::leanh::lean_dec_ref(v___f_2880_);
                        crate::leanh::lean_dec_ref(v___x_2879_);
                        v___x_2966_ = crate::leanh::lean_box(0);
                        v___x_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                        return v___x_2967_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_2882_);
                    crate::leanh::lean_dec_ref(v_ci_2881_);
                    crate::leanh::lean_dec_ref(v___f_2880_);
                    crate::leanh::lean_dec_ref(v___x_2879_);
                    v___x_2968_ = crate::leanh::lean_box(0);
                    v___x_2969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                    return v___x_2969_;
                }
            }
            1 => {
                v_parentDecl_x3f_2894_ = crate::leanh::lean_ctor_get(v_ci_2881_, 1);
                v_autoImplicits_2895_ = crate::leanh::lean_ctor_get(v_ci_2881_, 2);
                v_isSharedCheck_2963_ = (!crate::leanh::lean_is_exclusive(v_ci_2881_)) as u8;
                if v_isSharedCheck_2963_ == 0 {
                    v_unused_2964_ = crate::leanh::lean_ctor_get(v_ci_2881_, 0);
                    crate::leanh::lean_dec(v_unused_2964_);
                    v___x_2897_ = v_ci_2881_;
                    v_isShared_2898_ = v_isSharedCheck_2963_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_autoImplicits_2895_);
                    crate::leanh::lean_inc(v_parentDecl_x3f_2894_);
                    crate::leanh::lean_dec(v_ci_2881_);
                    v___x_2897_ = crate::leanh::lean_box(0);
                    v_isShared_2898_ = v_isSharedCheck_2963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_env_2899_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 0);
                v_cmdEnv_x3f_2900_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 1);
                v_fileMap_2901_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 2);
                v_options_2902_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 4);
                v_currNamespace_2903_ =
                    crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 5);
                v_openDecls_2904_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 6);
                v_ngen_2905_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 7);
                v_isSharedCheck_2961_ =
                    (!crate::leanh::lean_is_exclusive(v_toCommandContextInfo_2889_)) as u8;
                if v_isSharedCheck_2961_ == 0 {
                    v_unused_2962_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 3);
                    crate::leanh::lean_dec(v_unused_2962_);
                    v___x_2907_ = v_toCommandContextInfo_2889_;
                    v_isShared_2908_ = v_isSharedCheck_2961_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_2905_);
                    crate::leanh::lean_inc(v_openDecls_2904_);
                    crate::leanh::lean_inc(v_currNamespace_2903_);
                    crate::leanh::lean_inc(v_options_2902_);
                    crate::leanh::lean_inc(v_fileMap_2901_);
                    crate::leanh::lean_inc(v_cmdEnv_x3f_2900_);
                    crate::leanh::lean_inc(v_env_2899_);
                    crate::leanh::lean_dec(v_toCommandContextInfo_2889_);
                    v___x_2907_ = crate::leanh::lean_box(0);
                    v_isShared_2908_ = v_isSharedCheck_2961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toElabInfo_2909_ = crate::leanh::lean_ctor_get(v_i_2890_, 0);
                crate::leanh::lean_inc_ref(v_toElabInfo_2909_);
                v_mctxBefore_2910_ = crate::leanh::lean_ctor_get(v_i_2890_, 1);
                crate::leanh::lean_inc_ref(v_mctxBefore_2910_);
                v_goalsBefore_2911_ = crate::leanh::lean_ctor_get(v_i_2890_, 2);
                crate::leanh::lean_inc(v_goalsBefore_2911_);
                v_mctxAfter_2912_ = crate::leanh::lean_ctor_get(v_i_2890_, 3);
                crate::leanh::lean_inc_ref(v_mctxAfter_2912_);
                v_goalsAfter_2913_ = crate::leanh::lean_ctor_get(v_i_2890_, 4);
                crate::leanh::lean_inc(v_goalsAfter_2913_);
                crate::leanh::lean_dec_ref(v_i_2890_);
                crate::leanh::lean_inc_ref(v_ngen_2905_);
                crate::leanh::lean_inc(v_openDecls_2904_);
                crate::leanh::lean_inc(v_currNamespace_2903_);
                crate::leanh::lean_inc_ref(v_options_2902_);
                crate::leanh::lean_inc_ref(v_fileMap_2901_);
                crate::leanh::lean_inc(v_cmdEnv_x3f_2900_);
                crate::leanh::lean_inc_ref(v_env_2899_);
                if v_isShared_2908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2907_, 3, v_mctxBefore_2910_);
                    v___x_2946_ = v___x_2907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_env_2899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_cmdEnv_x3f_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_fileMap_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_mctxBefore_2910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_options_2902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_currNamespace_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 6, v_openDecls_2904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 7, v_ngen_2905_);
                    v___x_2946_ = v_reuseFailAlloc_2960_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_2915_) == 0 {
                    crate::leanh::lean_del_object(v___x_2892_);
                    v_a_2916_ = crate::leanh::lean_ctor_get(v___y_2915_, 0);
                    v_isSharedCheck_2929_ = (!crate::leanh::lean_is_exclusive(v___y_2915_)) as u8;
                    if v_isSharedCheck_2929_ == 0 {
                        v___x_2918_ = v___y_2915_;
                        v_isShared_2919_ = v_isSharedCheck_2929_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2916_);
                        crate::leanh::lean_dec(v___y_2915_);
                        v___x_2918_ = crate::leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2929_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toElabInfo_2909_);
                    crate::leanh::lean_dec_ref(v___x_2879_);
                    v_a_2930_ = crate::leanh::lean_ctor_get(v___y_2915_, 0);
                    v_isSharedCheck_2944_ = (!crate::leanh::lean_is_exclusive(v___y_2915_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2932_ = v___y_2915_;
                        v_isShared_2933_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2930_);
                        crate::leanh::lean_dec(v___y_2915_);
                        v___x_2932_ = crate::leanh::lean_box(0);
                        v_isShared_2933_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_2916_) == 1 {
                    crate::leanh::lean_del_object(v___x_2918_);
                    v_val_2920_ = crate::leanh::lean_ctor_get(v_a_2916_, 0);
                    crate::leanh::lean_inc(v_val_2920_);
                    crate::leanh::lean_dec_ref_known(v_a_2916_, 1);
                    v___x_2921_ = crate::leanh::lean_box((v_a_2878_) as usize);
                    v___x_2922_ = lean_st_ref_set(v_val_2877_, v___x_2921_);
                    v_stx_2923_ = crate::leanh::lean_ctor_get(v_toElabInfo_2909_, 1);
                    crate::leanh::lean_inc(v_stx_2923_);
                    crate::leanh::lean_dec_ref(v_toElabInfo_2909_);
                    v___x_2924_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___x_2879_, v_stx_2923_, v_val_2920_, v___y_2884_, v___y_2885_);
                    crate::leanh::lean_dec(v_stx_2923_);
                    return v___x_2924_;
                } else {
                    crate::leanh::lean_dec(v_a_2916_);
                    crate::leanh::lean_dec_ref(v_toElabInfo_2909_);
                    crate::leanh::lean_dec_ref(v___x_2879_);
                    v___x_2925_ = crate::leanh::lean_box(0);
                    if v_isShared_2919_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2918_, 0, v___x_2925_);
                        v___x_2927_ = v___x_2918_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
                        v___x_2927_ = v_reuseFailAlloc_2928_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2927_;
            }
            7 => {
                v_ref_2934_ = crate::leanh::lean_ctor_get(v___y_2884_, 7);
                v___x_2935_ = lean_io_error_to_string(v_a_2930_);
                if v_isShared_2893_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2892_, 3);
                    crate::leanh::lean_ctor_set(v___x_2892_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2892_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2935_);
                    v___x_2937_ = v_reuseFailAlloc_2943_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2938_ = l_Lean_MessageData_ofFormat(v___x_2937_);
                crate::leanh::lean_inc(v_ref_2934_);
                v___x_2939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2939_, 0, v_ref_2934_);
                crate::leanh::lean_ctor_set(v___x_2939_, 1, v___x_2938_);
                if v_isShared_2933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2932_, 0, v___x_2939_);
                    v___x_2941_ = v___x_2932_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2941_;
            }
            10 => {
                crate::leanh::lean_inc_ref(v_autoImplicits_2895_);
                crate::leanh::lean_inc(v_parentDecl_x3f_2894_);
                if v_isShared_2898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2897_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2897_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_parentDecl_x3f_2894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_autoImplicits_2895_);
                    v___x_2948_ = v_reuseFailAlloc_2959_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2);
                v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3;
                crate::leanh::lean_inc_ref(v___f_2880_);
                v___x_2951_ =
                    crate::leanh::lean_apply_2(v___f_2880_, v___x_2950_, v_goalsBefore_2911_);
                v___x_2952_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                    v___x_2948_,
                    v___x_2949_,
                    v___x_2951_,
                );
                if crate::leanh::lean_obj_tag(v___x_2952_) == 0 {
                    v_a_2953_ = crate::leanh::lean_ctor_get(v___x_2952_, 0);
                    crate::leanh::lean_inc(v_a_2953_);
                    if crate::leanh::lean_obj_tag(v_a_2953_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2952_, 1);
                        v___x_2954_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2954_, 0, v_env_2899_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 1, v_cmdEnv_x3f_2900_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 2, v_fileMap_2901_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 3, v_mctxAfter_2912_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 4, v_options_2902_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 5, v_currNamespace_2903_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 6, v_openDecls_2904_);
                        crate::leanh::lean_ctor_set(v___x_2954_, 7, v_ngen_2905_);
                        v___x_2955_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2955_, 0, v___x_2954_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 1, v_parentDecl_x3f_2894_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 2, v_autoImplicits_2895_);
                        v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4;
                        v___x_2957_ = crate::leanh::lean_apply_2(
                            v___f_2880_,
                            v___x_2956_,
                            v_goalsAfter_2913_,
                        );
                        v___x_2958_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                            v___x_2955_,
                            v___x_2949_,
                            v___x_2957_,
                        );
                        v___y_2915_ = v___x_2958_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_2953_, 1);
                        crate::leanh::lean_dec(v_goalsAfter_2913_);
                        crate::leanh::lean_dec_ref(v_mctxAfter_2912_);
                        crate::leanh::lean_dec_ref(v_ngen_2905_);
                        crate::leanh::lean_dec(v_openDecls_2904_);
                        crate::leanh::lean_dec(v_currNamespace_2903_);
                        crate::leanh::lean_dec_ref(v_options_2902_);
                        crate::leanh::lean_dec_ref(v_fileMap_2901_);
                        crate::leanh::lean_dec(v_cmdEnv_x3f_2900_);
                        crate::leanh::lean_dec_ref(v_env_2899_);
                        crate::leanh::lean_dec_ref(v_autoImplicits_2895_);
                        crate::leanh::lean_dec(v_parentDecl_x3f_2894_);
                        crate::leanh::lean_dec_ref(v___f_2880_);
                        v___y_2915_ = v___x_2952_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goalsAfter_2913_);
                    crate::leanh::lean_dec_ref(v_mctxAfter_2912_);
                    crate::leanh::lean_dec_ref(v_ngen_2905_);
                    crate::leanh::lean_dec(v_openDecls_2904_);
                    crate::leanh::lean_dec(v_currNamespace_2903_);
                    crate::leanh::lean_dec_ref(v_options_2902_);
                    crate::leanh::lean_dec_ref(v_fileMap_2901_);
                    crate::leanh::lean_dec(v_cmdEnv_x3f_2900_);
                    crate::leanh::lean_dec_ref(v_env_2899_);
                    crate::leanh::lean_dec_ref(v_autoImplicits_2895_);
                    crate::leanh::lean_dec(v_parentDecl_x3f_2894_);
                    crate::leanh::lean_dec_ref(v___f_2880_);
                    v___y_2915_ = v___x_2952_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed(
    mut v_val_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v___x_2972_: *mut crate::leanh::LeanObject,
    mut v___f_2973_: *mut crate::leanh::LeanObject,
    mut v_ci_2974_: *mut crate::leanh::LeanObject,
    mut v_info_2975_: *mut crate::leanh::LeanObject,
    mut v_x_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
    mut v___y_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_29890__boxed_2980_: u8 = 0;
    let mut v_res_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_29890__boxed_2980_ = (crate::leanh::lean_unbox(v_a_2971_) as u8);
    v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(v_val_2970_, v_a_29890__boxed_2980_, v___x_2972_, v___f_2973_, v_ci_2974_, v_info_2975_, v_x_2976_, v___y_2977_, v___y_2978_);
    crate::leanh::lean_dec(v___y_2978_);
    crate::leanh::lean_dec_ref(v___y_2977_);
    crate::leanh::lean_dec_ref(v_x_2976_);
    crate::leanh::lean_dec(v_val_2970_);
    return v_res_2981_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(
    mut v___x_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_a_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2993_: u8 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2983_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_2982_);
                    v___x_2985_ = lean_array_to_list(v_a_2984_);
                    return v___x_2985_;
                } else {
                    v_head_2986_ = crate::leanh::lean_ctor_get(v_a_2983_, 0);
                    crate::leanh::lean_inc(v_head_2986_);
                    v_tail_2987_ = crate::leanh::lean_ctor_get(v_a_2983_, 1);
                    crate::leanh::lean_inc(v_tail_2987_);
                    crate::leanh::lean_dec_ref_known(v_a_2983_, 2);
                    v_fst_2988_ = crate::leanh::lean_ctor_get(v_head_2986_, 0);
                    crate::leanh::lean_inc(v_fst_2988_);
                    v_snd_2989_ = crate::leanh::lean_ctor_get(v_head_2986_, 1);
                    crate::leanh::lean_inc(v_snd_2989_);
                    crate::leanh::lean_dec(v_head_2986_);
                    v___x_2990_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2991_ = lean_nat_dec_lt(v___x_2990_, v_snd_2989_);
                    crate::leanh::lean_dec(v_snd_2989_);
                    if v___x_2991_ == 0 {
                        crate::leanh::lean_dec(v_fst_2988_);
                        v_a_2983_ = v_tail_2987_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2988_);
                        crate::leanh::lean_inc_ref(v___x_2982_);
                        v___x_2993_ = lean_get_reducibility_status(v___x_2982_, v_fst_2988_);
                        if v___x_2993_ == 1 {
                            crate::leanh::lean_inc_ref(v___x_2982_);
                            v___x_2994_ = l_Lean_Meta_isInstanceCore(v___x_2982_, v_fst_2988_);
                            if v___x_2994_ == 0 {
                                v___x_2995_ =
                                    l_Lean_MessageData_ofConstName(v_fst_2988_, v___x_2994_);
                                v___x_2996_ = lean_array_push(v_a_2984_, v___x_2995_);
                                v_a_2983_ = v_tail_2987_;
                                v_a_2984_ = v___x_2996_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_fst_2988_);
                                v_a_2983_ = v_tail_2987_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_2988_);
                            v_a_2983_ = v_tail_2987_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(
    mut v_o_3002_: *mut crate::leanh::LeanObject,
    mut v_k_3003_: *mut crate::leanh::LeanObject,
    mut v_v_3004_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3006_: u8 = 0;
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3005_ = crate::leanh::lean_ctor_get(v_o_3002_, 0);
                v_hasTrace_3006_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_3002_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3020_ = (!crate::leanh::lean_is_exclusive(v_o_3002_)) as u8;
                if v_isSharedCheck_3020_ == 0 {
                    v___x_3008_ = v_o_3002_;
                    v_isShared_3009_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_3005_);
                    crate::leanh::lean_dec(v_o_3002_);
                    v___x_3008_ = crate::leanh::lean_box(0);
                    v_isShared_3009_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3010_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_3010_, 0 as u32, v_v_3004_);
                crate::leanh::lean_inc(v_k_3003_);
                v___x_3011_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3003_, v___x_3010_, v_map_3005_);
                if v_hasTrace_3006_ == 0 {
                    v___x_3012_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0;
                    v___x_3013_ = l_Lean_Name_isPrefixOf(v___x_3012_, v_k_3003_);
                    crate::leanh::lean_dec(v_k_3003_);
                    if v_isShared_3009_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3011_);
                        v___x_3015_ = v___x_3008_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3011_);
                        v___x_3015_ = v_reuseFailAlloc_3016_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3003_);
                    if v_isShared_3009_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3011_);
                        v___x_3018_ = v___x_3008_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3011_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3019_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3006_,
                        );
                        v___x_3018_ = v_reuseFailAlloc_3019_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3015_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3013_,
                );
                return v___x_3015_;
            }
            3 => {
                return v___x_3018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___boxed(
    mut v_o_3021_: *mut crate::leanh::LeanObject,
    mut v_k_3022_: *mut crate::leanh::LeanObject,
    mut v_v_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_3024_: u8 = 0;
    let mut v_res_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3024_ = (crate::leanh::lean_unbox(v_v_3023_) as u8);
    v_res_3025_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_o_3021_, v_k_3022_, v_v_boxed_3024_);
    return v_res_3025_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(
    mut v_opts_3026_: *mut crate::leanh::LeanObject,
    mut v_opt_3027_: *mut crate::leanh::LeanObject,
    mut v_val_3028_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3029_ = crate::leanh::lean_ctor_get(v_opt_3027_, 0);
    crate::leanh::lean_inc(v_name_3029_);
    crate::leanh::lean_dec_ref(v_opt_3027_);
    v___x_3030_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_opts_3026_, v_name_3029_, v_val_3028_);
    return v___x_3030_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(
    mut v_opts_3031_: *mut crate::leanh::LeanObject,
    mut v_opt_3032_: *mut crate::leanh::LeanObject,
    mut v_val_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_3034_: u8 = 0;
    let mut v_res_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_3034_ = (crate::leanh::lean_unbox(v_val_3033_) as u8);
    v_res_3035_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_3031_, v_opt_3032_, v_val_boxed_3034_);
    return v_res_3035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(
    mut v_f_3036_: *mut crate::leanh::LeanObject,
    mut v_keys_3037_: *mut crate::leanh::LeanObject,
    mut v_vals_3038_: *mut crate::leanh::LeanObject,
    mut v_i_3039_: *mut crate::leanh::LeanObject,
    mut v_acc_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3041_ = lean_array_get_size(v_keys_3037_);
                v___x_3042_ = lean_nat_dec_lt(v_i_3039_, v___x_3041_);
                if v___x_3042_ == 0 {
                    crate::leanh::lean_dec(v_i_3039_);
                    crate::leanh::lean_dec_ref(v_f_3036_);
                    v___x_3043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3043_, 0, v_acc_3040_);
                    return v___x_3043_;
                } else {
                    v_k_3044_ = lean_array_fget_borrowed(v_keys_3037_, v_i_3039_);
                    v_v_3045_ = lean_array_fget_borrowed(v_vals_3038_, v_i_3039_);
                    crate::leanh::lean_inc_ref(v_f_3036_);
                    crate::leanh::lean_inc(v_v_3045_);
                    crate::leanh::lean_inc(v_k_3044_);
                    v___x_3046_ =
                        crate::leanh::lean_apply_3(v_f_3036_, v_acc_3040_, v_k_3044_, v_v_3045_);
                    if crate::leanh::lean_obj_tag(v___x_3046_) == 0 {
                        crate::leanh::lean_dec(v_i_3039_);
                        crate::leanh::lean_dec_ref(v_f_3036_);
                        return v___x_3046_;
                    } else {
                        v_a_3047_ = crate::leanh::lean_ctor_get(v___x_3046_, 0);
                        crate::leanh::lean_inc(v_a_3047_);
                        crate::leanh::lean_dec_ref_known(v___x_3046_, 1);
                        v___x_3048_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3049_ = lean_nat_add(v_i_3039_, v___x_3048_);
                        crate::leanh::lean_dec(v_i_3039_);
                        v_i_3039_ = v___x_3049_;
                        v_acc_3040_ = v_a_3047_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg___boxed(
    mut v_f_3051_: *mut crate::leanh::LeanObject,
    mut v_keys_3052_: *mut crate::leanh::LeanObject,
    mut v_vals_3053_: *mut crate::leanh::LeanObject,
    mut v_i_3054_: *mut crate::leanh::LeanObject,
    mut v_acc_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_3051_, v_keys_3052_, v_vals_3053_, v_i_3054_, v_acc_3055_);
    crate::leanh::lean_dec_ref(v_vals_3053_);
    crate::leanh::lean_dec_ref(v_keys_3052_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(
    mut v_f_3057_: *mut crate::leanh::LeanObject,
    mut v_x_3058_: *mut crate::leanh::LeanObject,
    mut v_x_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: usize = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_ks_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3058_) == 0 {
                    v_es_3060_ = crate::leanh::lean_ctor_get(v_x_3058_, 0);
                    v_isSharedCheck_3080_ = (!crate::leanh::lean_is_exclusive(v_x_3058_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3062_ = v_x_3058_;
                        v_isShared_3063_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_3060_);
                        crate::leanh::lean_dec(v_x_3058_);
                        v___x_3062_ = crate::leanh::lean_box(0);
                        v_isShared_3063_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3081_ = crate::leanh::lean_ctor_get(v_x_3058_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3081_);
                    v_vs_3082_ = crate::leanh::lean_ctor_get(v_x_3058_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3082_);
                    crate::leanh::lean_dec_ref_known(v_x_3058_, 2);
                    v___x_3083_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_3057_, v_ks_3081_, v_vs_3082_, v___x_3083_, v_x_3059_);
                    crate::leanh::lean_dec_ref(v_vs_3082_);
                    crate::leanh::lean_dec_ref(v_ks_3081_);
                    return v___x_3084_;
                }
            }
            1 => {
                v___x_3064_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3065_ = lean_array_get_size(v_es_3060_);
                v___x_3066_ = lean_nat_dec_lt(v___x_3064_, v___x_3065_);
                if v___x_3066_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_3060_);
                    crate::leanh::lean_dec_ref(v_f_3057_);
                    if v_isShared_3063_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3062_, 1);
                        crate::leanh::lean_ctor_set(v___x_3062_, 0, v_x_3059_);
                        v___x_3068_ = v___x_3062_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_x_3059_);
                        v___x_3068_ = v_reuseFailAlloc_3069_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3070_ = lean_nat_dec_le(v___x_3065_, v___x_3065_);
                    if v___x_3070_ == 0 {
                        if v___x_3066_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_3060_);
                            crate::leanh::lean_dec_ref(v_f_3057_);
                            if v_isShared_3063_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3062_, 1);
                                crate::leanh::lean_ctor_set(v___x_3062_, 0, v_x_3059_);
                                v___x_3072_ = v___x_3062_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3073_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_x_3059_);
                                v___x_3072_ = v_reuseFailAlloc_3073_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3062_);
                            v___x_3074_ = 0usize;
                            v___x_3075_ = lean_usize_of_nat(v___x_3065_);
                            v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3057_, v_es_3060_, v___x_3074_, v___x_3075_, v_x_3059_);
                            crate::leanh::lean_dec_ref(v_es_3060_);
                            return v___x_3076_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3062_);
                        v___x_3077_ = 0usize;
                        v___x_3078_ = lean_usize_of_nat(v___x_3065_);
                        v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3057_, v_es_3060_, v___x_3077_, v___x_3078_, v_x_3059_);
                        crate::leanh::lean_dec_ref(v_es_3060_);
                        return v___x_3079_;
                    }
                }
            }
            2 => {
                return v___x_3068_;
            }
            3 => {
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(
    mut v_f_3085_: *mut crate::leanh::LeanObject,
    mut v_as_3086_: *mut crate::leanh::LeanObject,
    mut v_i_3087_: usize,
    mut v_stop_3088_: usize,
    mut v_b_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: usize = 0;
    let mut v___x_3093_: usize = 0;
    let mut v___y_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3098_ = lean_usize_dec_eq(v_i_3087_, v_stop_3088_);
                if v___x_3098_ == 0 {
                    v___x_3099_ = lean_array_uget_borrowed(v_as_3086_, v_i_3087_);
                    match crate::leanh::lean_obj_tag(v___x_3099_) {
                        0 => {
                            v_key_3100_ = crate::leanh::lean_ctor_get(v___x_3099_, 0);
                            v_val_3101_ = crate::leanh::lean_ctor_get(v___x_3099_, 1);
                            crate::leanh::lean_inc_ref(v_f_3085_);
                            crate::leanh::lean_inc(v_val_3101_);
                            crate::leanh::lean_inc(v_key_3100_);
                            v___x_3102_ = crate::leanh::lean_apply_3(
                                v_f_3085_,
                                v_b_3089_,
                                v_key_3100_,
                                v_val_3101_,
                            );
                            v___y_3096_ = v___x_3102_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3103_ = crate::leanh::lean_ctor_get(v___x_3099_, 0);
                            crate::leanh::lean_inc(v_node_3103_);
                            crate::leanh::lean_inc_ref(v_f_3085_);
                            v___x_3104_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_3085_, v_node_3103_, v_b_3089_);
                            v___y_3096_ = v___x_3104_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_3091_ = v_b_3089_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3085_);
                    v___x_3105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3105_, 0, v_b_3089_);
                    return v___x_3105_;
                }
            }
            1 => {
                v___x_3092_ = 1usize;
                v___x_3093_ = lean_usize_add(v_i_3087_, v___x_3092_);
                v_i_3087_ = v___x_3093_;
                v_b_3089_ = v_a_3091_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3096_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_3085_);
                    return v___y_3096_;
                } else {
                    v_a_3097_ = crate::leanh::lean_ctor_get(v___y_3096_, 0);
                    crate::leanh::lean_inc(v_a_3097_);
                    crate::leanh::lean_dec_ref_known(v___y_3096_, 1);
                    v_a_3091_ = v_a_3097_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg___boxed(
    mut v_f_3106_: *mut crate::leanh::LeanObject,
    mut v_as_3107_: *mut crate::leanh::LeanObject,
    mut v_i_3108_: *mut crate::leanh::LeanObject,
    mut v_stop_3109_: *mut crate::leanh::LeanObject,
    mut v_b_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3111_: usize = 0;
    let mut v_stop_boxed_3112_: usize = 0;
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3111_ = crate::leanh::lean_unbox_usize(v_i_3108_);
    crate::leanh::lean_dec(v_i_3108_);
    v_stop_boxed_3112_ = crate::leanh::lean_unbox_usize(v_stop_3109_);
    crate::leanh::lean_dec(v_stop_3109_);
    v_res_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3106_, v_as_3107_, v_i_boxed_3111_, v_stop_boxed_3112_, v_b_3110_);
    crate::leanh::lean_dec_ref(v_as_3107_);
    return v_res_3113_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(
    mut v_f_3114_: *mut crate::leanh::LeanObject,
    mut v_s_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
    mut v_b_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_a_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3118_, 0, v_a_3116_);
                crate::leanh::lean_ctor_set(v___x_3118_, 1, v_b_3117_);
                v___x_3119_ = crate::leanh::lean_apply_2(v_f_3114_, v___x_3118_, v_s_3115_);
                if crate::leanh::lean_obj_tag(v___x_3119_) == 0 {
                    v_a_3120_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3127_ = (!crate::leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v___x_3122_ = v___x_3119_;
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3120_);
                        crate::leanh::lean_dec(v___x_3119_);
                        v___x_3122_ = crate::leanh::lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!crate::leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3128_);
                        crate::leanh::lean_dec(v___x_3119_);
                        v___x_3130_ = crate::leanh::lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3123_ == 0 {
                    v___x_3125_ = v___x_3122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3125_;
            }
            3 => {
                if v_isShared_3131_ == 0 {
                    v___x_3133_ = v___x_3130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(
    mut v_map_3136_: *mut crate::leanh::LeanObject,
    mut v_init_3137_: *mut crate::leanh::LeanObject,
    mut v_f_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3139_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3139_, 0, v_f_3138_);
    crate::leanh::lean_inc_ref(v_map_3136_);
    v___x_3140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v___f_3139_, v_map_3136_, v_init_3137_);
    v_a_3141_ = crate::leanh::lean_ctor_get(v___x_3140_, 0);
    crate::leanh::lean_inc(v_a_3141_);
    crate::leanh::lean_dec_ref(v___x_3140_);
    return v_a_3141_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(
    mut v_map_3142_: *mut crate::leanh::LeanObject,
    mut v_init_3143_: *mut crate::leanh::LeanObject,
    mut v_f_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_3142_, v_init_3143_, v_f_3144_);
    crate::leanh::lean_dec_ref(v_map_3142_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(
    mut v_x_3146_: *mut crate::leanh::LeanObject,
    mut v_x_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v_x_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3150_ = crate::leanh::lean_ctor_get(v_x_3146_, 0);
                v_vs_3151_ = crate::leanh::lean_ctor_get(v_x_3146_, 1);
                v_isSharedCheck_3175_ = (!crate::leanh::lean_is_exclusive(v_x_3146_)) as u8;
                if v_isSharedCheck_3175_ == 0 {
                    v___x_3153_ = v_x_3146_;
                    v_isShared_3154_ = v_isSharedCheck_3175_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3151_);
                    crate::leanh::lean_inc(v_ks_3150_);
                    crate::leanh::lean_dec(v_x_3146_);
                    v___x_3153_ = crate::leanh::lean_box(0);
                    v_isShared_3154_ = v_isSharedCheck_3175_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3155_ = lean_array_get_size(v_ks_3150_);
                v___x_3156_ = lean_nat_dec_lt(v_x_3147_, v___x_3155_);
                if v___x_3156_ == 0 {
                    crate::leanh::lean_dec(v_x_3147_);
                    v___x_3157_ = lean_array_push(v_ks_3150_, v_x_3148_);
                    v___x_3158_ = lean_array_push(v_vs_3151_, v_x_3149_);
                    if v_isShared_3154_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3153_, 1, v___x_3158_);
                        crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3157_);
                        v___x_3160_ = v___x_3153_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3161_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3157_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___x_3158_);
                        v___x_3160_ = v_reuseFailAlloc_3161_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3162_ = lean_array_fget_borrowed(v_ks_3150_, v_x_3147_);
                    v___x_3163_ = lean_name_eq(v_x_3148_, v_k_x27_3162_);
                    if v___x_3163_ == 0 {
                        if v_isShared_3154_ == 0 {
                            v___x_3165_ = v___x_3153_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3169_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_ks_3150_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_vs_3151_);
                            v___x_3165_ = v_reuseFailAlloc_3169_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3170_ = lean_array_fset(v_ks_3150_, v_x_3147_, v_x_3148_);
                        v___x_3171_ = lean_array_fset(v_vs_3151_, v_x_3147_, v_x_3149_);
                        crate::leanh::lean_dec(v_x_3147_);
                        if v_isShared_3154_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3153_, 1, v___x_3171_);
                            crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3170_);
                            v___x_3173_ = v___x_3153_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3174_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3170_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3171_);
                            v___x_3173_ = v_reuseFailAlloc_3174_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3160_;
            }
            3 => {
                v___x_3166_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3167_ = lean_nat_add(v_x_3147_, v___x_3166_);
                crate::leanh::lean_dec(v_x_3147_);
                v_x_3146_ = v___x_3165_;
                v_x_3147_ = v___x_3167_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(
    mut v_n_3176_: *mut crate::leanh::LeanObject,
    mut v_k_3177_: *mut crate::leanh::LeanObject,
    mut v_v_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3180_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_n_3176_, v___x_3179_, v_k_3177_, v_v_3178_);
    return v___x_3180_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0()
-> u64 {
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u64 = 0;
    v___x_3181_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3182_ = lean_uint64_of_nat(v___x_3181_);
    return v___x_3182_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0()
-> usize {
    let mut v___x_3183_: usize = 0;
    let mut v___x_3184_: usize = 0;
    let mut v___x_3185_: usize = 0;
    v___x_3183_ = 5usize;
    v___x_3184_ = 1usize;
    v___x_3185_ = lean_usize_shift_left(v___x_3184_, v___x_3183_);
    return v___x_3185_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1()
-> usize {
    let mut v___x_3186_: usize = 0;
    let mut v___x_3187_: usize = 0;
    let mut v___x_3188_: usize = 0;
    v___x_3186_ = 1usize;
    v___x_3187_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0);
    v___x_3188_ = lean_usize_sub(v___x_3187_, v___x_3186_);
    return v___x_3188_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3189_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(
    mut v_x_3190_: *mut crate::leanh::LeanObject,
    mut v_x_3191_: usize,
    mut v_x_3192_: usize,
    mut v_x_3193_: *mut crate::leanh::LeanObject,
    mut v_x_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v_j_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v_v_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v_node_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_unused_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: u8 = 0;
    let mut v_ks_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: usize = 0;
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v_reuseFailAlloc_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3190_) == 0 {
                    v_es_3195_ = crate::leanh::lean_ctor_get(v_x_3190_, 0);
                    v___x_3196_ = 5usize;
                    v___x_3197_ = 1usize;
                    v___x_3198_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
                    v___x_3199_ = lean_usize_land(v_x_3191_, v___x_3198_);
                    v_j_3200_ = lean_usize_to_nat(v___x_3199_);
                    v___x_3201_ = lean_array_get_size(v_es_3195_);
                    v___x_3202_ = lean_nat_dec_lt(v_j_3200_, v___x_3201_);
                    if v___x_3202_ == 0 {
                        crate::leanh::lean_dec(v_j_3200_);
                        crate::leanh::lean_dec(v_x_3194_);
                        crate::leanh::lean_dec(v_x_3193_);
                        return v_x_3190_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3195_);
                        v_isSharedCheck_3239_ = (!crate::leanh::lean_is_exclusive(v_x_3190_)) as u8;
                        if v_isSharedCheck_3239_ == 0 {
                            v_unused_3240_ = crate::leanh::lean_ctor_get(v_x_3190_, 0);
                            crate::leanh::lean_dec(v_unused_3240_);
                            v___x_3204_ = v_x_3190_;
                            v_isShared_3205_ = v_isSharedCheck_3239_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3190_);
                            v___x_3204_ = crate::leanh::lean_box(0);
                            v_isShared_3205_ = v_isSharedCheck_3239_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3241_ = crate::leanh::lean_ctor_get(v_x_3190_, 0);
                    v_vs_3242_ = crate::leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3262_ = (!crate::leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3244_ = v_x_3190_;
                        v_isShared_3245_ = v_isSharedCheck_3262_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3242_);
                        crate::leanh::lean_inc(v_ks_3241_);
                        crate::leanh::lean_dec(v_x_3190_);
                        v___x_3244_ = crate::leanh::lean_box(0);
                        v_isShared_3245_ = v_isSharedCheck_3262_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3206_ = lean_array_fget(v_es_3195_, v_j_3200_);
                v___x_3207_ = crate::leanh::lean_box(0);
                v_xs_x27_3208_ = lean_array_fset(v_es_3195_, v_j_3200_, v___x_3207_);
                match crate::leanh::lean_obj_tag(v_v_3206_) {
                    0 => {
                        v_key_3215_ = crate::leanh::lean_ctor_get(v_v_3206_, 0);
                        v_val_3216_ = crate::leanh::lean_ctor_get(v_v_3206_, 1);
                        v_isSharedCheck_3226_ = (!crate::leanh::lean_is_exclusive(v_v_3206_)) as u8;
                        if v_isSharedCheck_3226_ == 0 {
                            v___x_3218_ = v_v_3206_;
                            v_isShared_3219_ = v_isSharedCheck_3226_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3216_);
                            crate::leanh::lean_inc(v_key_3215_);
                            crate::leanh::lean_dec(v_v_3206_);
                            v___x_3218_ = crate::leanh::lean_box(0);
                            v_isShared_3219_ = v_isSharedCheck_3226_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3227_ = crate::leanh::lean_ctor_get(v_v_3206_, 0);
                        v_isSharedCheck_3237_ = (!crate::leanh::lean_is_exclusive(v_v_3206_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3229_ = v_v_3206_;
                            v_isShared_3230_ = v_isSharedCheck_3237_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3227_);
                            crate::leanh::lean_dec(v_v_3206_);
                            v___x_3229_ = crate::leanh::lean_box(0);
                            v_isShared_3230_ = v_isSharedCheck_3237_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3238_, 0, v_x_3193_);
                        crate::leanh::lean_ctor_set(v___x_3238_, 1, v_x_3194_);
                        v___y_3210_ = v___x_3238_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3211_ = lean_array_fset(v_xs_x27_3208_, v_j_3200_, v___y_3210_);
                crate::leanh::lean_dec(v_j_3200_);
                if v_isShared_3205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3204_, 0, v___x_3211_);
                    v___x_3213_ = v___x_3204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
                    v___x_3213_ = v_reuseFailAlloc_3214_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3213_;
            }
            4 => {
                v___x_3220_ = lean_name_eq(v_x_3193_, v_key_3215_);
                if v___x_3220_ == 0 {
                    crate::leanh::lean_del_object(v___x_3218_);
                    v___x_3221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3215_,
                        v_val_3216_,
                        v_x_3193_,
                        v_x_3194_,
                    );
                    v___x_3222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3222_, 0, v___x_3221_);
                    v___y_3210_ = v___x_3222_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3216_);
                    crate::leanh::lean_dec(v_key_3215_);
                    if v_isShared_3219_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3218_, 1, v_x_3194_);
                        crate::leanh::lean_ctor_set(v___x_3218_, 0, v_x_3193_);
                        v___x_3224_ = v___x_3218_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_x_3193_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_x_3194_);
                        v___x_3224_ = v_reuseFailAlloc_3225_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3210_ = v___x_3224_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3231_ = lean_usize_shift_right(v_x_3191_, v___x_3196_);
                v___x_3232_ = lean_usize_add(v_x_3192_, v___x_3197_);
                v___x_3233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_node_3227_, v___x_3231_, v___x_3232_, v_x_3193_, v_x_3194_);
                if v_isShared_3230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3229_, 0, v___x_3233_);
                    v___x_3235_ = v___x_3229_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3210_ = v___x_3235_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3245_ == 0 {
                    v___x_3247_ = v___x_3244_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_ks_3241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_vs_3242_);
                    v___x_3247_ = v_reuseFailAlloc_3261_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3248_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v___x_3247_, v_x_3193_, v_x_3194_);
                v___x_3256_ = 7usize;
                v___x_3257_ = lean_usize_dec_le(v___x_3256_, v_x_3192_);
                if v___x_3257_ == 0 {
                    v___x_3258_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3248_);
                    v___x_3259_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3260_ = lean_nat_dec_lt(v___x_3258_, v___x_3259_);
                    crate::leanh::lean_dec(v___x_3258_);
                    v___y_3250_ = v___x_3260_;
                    state = 10;
                    continue;
                } else {
                    v___y_3250_ = v___x_3257_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3250_ == 0 {
                    v_ks_3251_ = crate::leanh::lean_ctor_get(v_newNode_3248_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3251_);
                    v_vs_3252_ = crate::leanh::lean_ctor_get(v_newNode_3248_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3252_);
                    crate::leanh::lean_dec_ref(v_newNode_3248_);
                    v___x_3253_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3254_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2);
                    v___x_3255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_x_3192_, v_ks_3251_, v_vs_3252_, v___x_3253_, v___x_3254_);
                    crate::leanh::lean_dec_ref(v_vs_3252_);
                    crate::leanh::lean_dec_ref(v_ks_3251_);
                    return v___x_3255_;
                } else {
                    return v_newNode_3248_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(
    mut v_depth_3263_: usize,
    mut v_keys_3264_: *mut crate::leanh::LeanObject,
    mut v_vals_3265_: *mut crate::leanh::LeanObject,
    mut v_i_3266_: *mut crate::leanh::LeanObject,
    mut v_entries_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v_k_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3273_: u64 = 0;
    let mut v_h_3274_: usize = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v_h_3280_: usize = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u64 = 0;
    let mut v_hash_3285_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3268_ = lean_array_get_size(v_keys_3264_);
                v___x_3269_ = lean_nat_dec_lt(v_i_3266_, v___x_3268_);
                if v___x_3269_ == 0 {
                    crate::leanh::lean_dec(v_i_3266_);
                    return v_entries_3267_;
                } else {
                    v_k_3270_ = lean_array_fget_borrowed(v_keys_3264_, v_i_3266_);
                    v_v_3271_ = lean_array_fget_borrowed(v_vals_3265_, v_i_3266_);
                    if crate::leanh::lean_obj_tag(v_k_3270_) == 0 {
                        v___x_3284_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                        v___y_3273_ = v___x_3284_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3285_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_3270_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3273_ = v_hash_3285_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3274_ = lean_uint64_to_usize(v___y_3273_);
                v___x_3275_ = 5usize;
                v___x_3276_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3277_ = 1usize;
                v___x_3278_ = lean_usize_sub(v_depth_3263_, v___x_3277_);
                v___x_3279_ = lean_usize_mul(v___x_3275_, v___x_3278_);
                v_h_3280_ = lean_usize_shift_right(v_h_3274_, v___x_3279_);
                v___x_3281_ = lean_nat_add(v_i_3266_, v___x_3276_);
                crate::leanh::lean_dec(v_i_3266_);
                crate::leanh::lean_inc(v_v_3271_);
                crate::leanh::lean_inc(v_k_3270_);
                v___x_3282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_entries_3267_, v_h_3280_, v_depth_3263_, v_k_3270_, v_v_3271_);
                v_i_3266_ = v___x_3281_;
                v_entries_3267_ = v___x_3282_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___boxed(
    mut v_depth_3286_: *mut crate::leanh::LeanObject,
    mut v_keys_3287_: *mut crate::leanh::LeanObject,
    mut v_vals_3288_: *mut crate::leanh::LeanObject,
    mut v_i_3289_: *mut crate::leanh::LeanObject,
    mut v_entries_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3291_: usize = 0;
    let mut v_res_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3291_ = crate::leanh::lean_unbox_usize(v_depth_3286_);
    crate::leanh::lean_dec(v_depth_3286_);
    v_res_3292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_boxed_3291_, v_keys_3287_, v_vals_3288_, v_i_3289_, v_entries_3290_);
    crate::leanh::lean_dec_ref(v_vals_3288_);
    crate::leanh::lean_dec_ref(v_keys_3287_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___boxed(
    mut v_x_3293_: *mut crate::leanh::LeanObject,
    mut v_x_3294_: *mut crate::leanh::LeanObject,
    mut v_x_3295_: *mut crate::leanh::LeanObject,
    mut v_x_3296_: *mut crate::leanh::LeanObject,
    mut v_x_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30371__boxed_3298_: usize = 0;
    let mut v_x_30372__boxed_3299_: usize = 0;
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30371__boxed_3298_ = crate::leanh::lean_unbox_usize(v_x_3294_);
    crate::leanh::lean_dec(v_x_3294_);
    v_x_30372__boxed_3299_ = crate::leanh::lean_unbox_usize(v_x_3295_);
    crate::leanh::lean_dec(v_x_3295_);
    v_res_3300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_3293_, v_x_30371__boxed_3298_, v_x_30372__boxed_3299_, v_x_3296_, v_x_3297_);
    return v_res_3300_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(
    mut v_x_3301_: *mut crate::leanh::LeanObject,
    mut v_x_3302_: *mut crate::leanh::LeanObject,
    mut v_x_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3305_: u64 = 0;
    let mut v___x_3306_: usize = 0;
    let mut v___x_3307_: usize = 0;
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u64 = 0;
    let mut v_hash_3310_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3302_) == 0 {
                    v___x_3309_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                    v___y_3305_ = v___x_3309_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3310_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3302_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3305_ = v_hash_3310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3306_ = lean_uint64_to_usize(v___y_3305_);
                v___x_3307_ = 1usize;
                v___x_3308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_3301_, v___x_3306_, v___x_3307_, v_x_3302_, v_x_3303_);
                return v___x_3308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(
    mut v_keys_3311_: *mut crate::leanh::LeanObject,
    mut v_vals_3312_: *mut crate::leanh::LeanObject,
    mut v_i_3313_: *mut crate::leanh::LeanObject,
    mut v_k_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3315_ = lean_array_get_size(v_keys_3311_);
                v___x_3316_ = lean_nat_dec_lt(v_i_3313_, v___x_3315_);
                if v___x_3316_ == 0 {
                    crate::leanh::lean_dec(v_i_3313_);
                    v___x_3317_ = crate::leanh::lean_box(0);
                    return v___x_3317_;
                } else {
                    v_k_x27_3318_ = lean_array_fget_borrowed(v_keys_3311_, v_i_3313_);
                    v___x_3319_ = lean_name_eq(v_k_3314_, v_k_x27_3318_);
                    if v___x_3319_ == 0 {
                        v___x_3320_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3321_ = lean_nat_add(v_i_3313_, v___x_3320_);
                        crate::leanh::lean_dec(v_i_3313_);
                        v_i_3313_ = v___x_3321_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3323_ = lean_array_fget_borrowed(v_vals_3312_, v_i_3313_);
                        crate::leanh::lean_dec(v_i_3313_);
                        crate::leanh::lean_inc(v___x_3323_);
                        v___x_3324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3324_, 0, v___x_3323_);
                        return v___x_3324_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg___boxed(
    mut v_keys_3325_: *mut crate::leanh::LeanObject,
    mut v_vals_3326_: *mut crate::leanh::LeanObject,
    mut v_i_3327_: *mut crate::leanh::LeanObject,
    mut v_k_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_3325_, v_vals_3326_, v_i_3327_, v_k_3328_);
    crate::leanh::lean_dec(v_k_3328_);
    crate::leanh::lean_dec_ref(v_vals_3326_);
    crate::leanh::lean_dec_ref(v_keys_3325_);
    return v_res_3329_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(
    mut v_x_3330_: *mut crate::leanh::LeanObject,
    mut v_x_3331_: usize,
    mut v_x_3332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: usize = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: usize = 0;
    let mut v_j_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: usize = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3330_) == 0 {
                    v_es_3333_ = crate::leanh::lean_ctor_get(v_x_3330_, 0);
                    v___x_3334_ = crate::leanh::lean_box(2);
                    v___x_3335_ = 5usize;
                    v___x_3336_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
                    v___x_3337_ = lean_usize_land(v_x_3331_, v___x_3336_);
                    v_j_3338_ = lean_usize_to_nat(v___x_3337_);
                    v___x_3339_ = lean_array_get_borrowed(v___x_3334_, v_es_3333_, v_j_3338_);
                    crate::leanh::lean_dec(v_j_3338_);
                    match crate::leanh::lean_obj_tag(v___x_3339_) {
                        0 => {
                            v_key_3340_ = crate::leanh::lean_ctor_get(v___x_3339_, 0);
                            v_val_3341_ = crate::leanh::lean_ctor_get(v___x_3339_, 1);
                            v___x_3342_ = lean_name_eq(v_x_3332_, v_key_3340_);
                            if v___x_3342_ == 0 {
                                v___x_3343_ = crate::leanh::lean_box(0);
                                return v___x_3343_;
                            } else {
                                crate::leanh::lean_inc(v_val_3341_);
                                v___x_3344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3344_, 0, v_val_3341_);
                                return v___x_3344_;
                            }
                        }
                        1 => {
                            v_node_3345_ = crate::leanh::lean_ctor_get(v___x_3339_, 0);
                            v___x_3346_ = lean_usize_shift_right(v_x_3331_, v___x_3335_);
                            v_x_3330_ = v_node_3345_;
                            v_x_3331_ = v___x_3346_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3348_ = crate::leanh::lean_box(0);
                            return v___x_3348_;
                        }
                    }
                } else {
                    v_ks_3349_ = crate::leanh::lean_ctor_get(v_x_3330_, 0);
                    v_vs_3350_ = crate::leanh::lean_ctor_get(v_x_3330_, 1);
                    v___x_3351_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3352_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_ks_3349_, v_vs_3350_, v___x_3351_, v_x_3332_);
                    return v___x_3352_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg___boxed(
    mut v_x_3353_: *mut crate::leanh::LeanObject,
    mut v_x_3354_: *mut crate::leanh::LeanObject,
    mut v_x_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30582__boxed_3356_: usize = 0;
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30582__boxed_3356_ = crate::leanh::lean_unbox_usize(v_x_3354_);
    crate::leanh::lean_dec(v_x_3354_);
    v_res_3357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_3353_, v_x_30582__boxed_3356_, v_x_3355_);
    crate::leanh::lean_dec(v_x_3355_);
    crate::leanh::lean_dec_ref(v_x_3353_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(
    mut v_x_3358_: *mut crate::leanh::LeanObject,
    mut v_x_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3361_: u64 = 0;
    let mut v___x_3362_: usize = 0;
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u64 = 0;
    let mut v_hash_3365_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3359_) == 0 {
                    v___x_3364_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                    v___y_3361_ = v___x_3364_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3365_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3359_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3361_ = v_hash_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3362_ = lean_uint64_to_usize(v___y_3361_);
                v___x_3363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_3358_, v___x_3362_, v_x_3359_);
                return v___x_3363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg___boxed(
    mut v_x_3366_: *mut crate::leanh::LeanObject,
    mut v_x_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_3366_, v_x_3367_);
    crate::leanh::lean_dec(v_x_3367_);
    crate::leanh::lean_dec_ref(v_x_3366_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(
    mut v_oldCounters_3369_: *mut crate::leanh::LeanObject,
    mut v_x_3370_: *mut crate::leanh::LeanObject,
    mut v_____s_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_result_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3372_ = crate::leanh::lean_ctor_get(v_x_3370_, 0);
                crate::leanh::lean_inc(v_fst_3372_);
                v_snd_3373_ = crate::leanh::lean_ctor_get(v_x_3370_, 1);
                crate::leanh::lean_inc(v_snd_3373_);
                crate::leanh::lean_dec_ref(v_x_3370_);
                v___x_3374_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_oldCounters_3369_, v_fst_3372_);
                if crate::leanh::lean_obj_tag(v___x_3374_) == 1 {
                    v_val_3375_ = crate::leanh::lean_ctor_get(v___x_3374_, 0);
                    v_isSharedCheck_3384_ = (!crate::leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3384_ == 0 {
                        v___x_3377_ = v___x_3374_;
                        v_isShared_3378_ = v_isSharedCheck_3384_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3375_);
                        crate::leanh::lean_dec(v___x_3374_);
                        v___x_3377_ = crate::leanh::lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3384_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3374_);
                    v_result_3385_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_3371_, v_fst_3372_, v_snd_3373_);
                    v___x_3386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3386_, 0, v_result_3385_);
                    return v___x_3386_;
                }
            }
            1 => {
                v___x_3379_ = lean_nat_sub(v_snd_3373_, v_val_3375_);
                crate::leanh::lean_dec(v_val_3375_);
                crate::leanh::lean_dec(v_snd_3373_);
                v_result_3380_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_3371_, v_fst_3372_, v___x_3379_);
                if v_isShared_3378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3377_, 0, v_result_3380_);
                    v___x_3382_ = v___x_3377_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_result_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed(
    mut v_oldCounters_3387_: *mut crate::leanh::LeanObject,
    mut v_x_3388_: *mut crate::leanh::LeanObject,
    mut v_____s_3389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3390_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(v_oldCounters_3387_, v_x_3388_, v_____s_3389_);
    crate::leanh::lean_dec_ref(v_oldCounters_3387_);
    return v_res_3390_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3391_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once), _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0);
    v_result_3393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v_result_3393_, 0, v___x_3392_);
    return v_result_3393_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(
    mut v_newCounters_3394_: *mut crate::leanh::LeanObject,
    mut v_oldCounters_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3396_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___f_3396_, 0, v_oldCounters_3395_);
    v_result_3397_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once), _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1);
    v___x_3398_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_newCounters_3394_, v_result_3397_, v___f_3396_);
    return v___x_3398_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___boxed(
    mut v_newCounters_3399_: *mut crate::leanh::LeanObject,
    mut v_oldCounters_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_newCounters_3399_, v_oldCounters_3400_);
    crate::leanh::lean_dec_ref(v_newCounters_3399_);
    return v_res_3401_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(
    mut v_f_3402_: *mut crate::leanh::LeanObject,
    mut v_keys_3403_: *mut crate::leanh::LeanObject,
    mut v_vals_3404_: *mut crate::leanh::LeanObject,
    mut v_i_3405_: *mut crate::leanh::LeanObject,
    mut v_acc_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    let mut v_k_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3407_ = lean_array_get_size(v_keys_3403_);
                v___x_3408_ = lean_nat_dec_lt(v_i_3405_, v___x_3407_);
                if v___x_3408_ == 0 {
                    crate::leanh::lean_dec(v_i_3405_);
                    crate::leanh::lean_dec(v_f_3402_);
                    return v_acc_3406_;
                } else {
                    v_k_3409_ = lean_array_fget_borrowed(v_keys_3403_, v_i_3405_);
                    v_v_3410_ = lean_array_fget_borrowed(v_vals_3404_, v_i_3405_);
                    crate::leanh::lean_inc(v_f_3402_);
                    crate::leanh::lean_inc(v_v_3410_);
                    crate::leanh::lean_inc(v_k_3409_);
                    v___x_3411_ =
                        crate::leanh::lean_apply_3(v_f_3402_, v_acc_3406_, v_k_3409_, v_v_3410_);
                    v___x_3412_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3413_ = lean_nat_add(v_i_3405_, v___x_3412_);
                    crate::leanh::lean_dec(v_i_3405_);
                    v_i_3405_ = v___x_3413_;
                    v_acc_3406_ = v___x_3411_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg___boxed(
    mut v_f_3415_: *mut crate::leanh::LeanObject,
    mut v_keys_3416_: *mut crate::leanh::LeanObject,
    mut v_vals_3417_: *mut crate::leanh::LeanObject,
    mut v_i_3418_: *mut crate::leanh::LeanObject,
    mut v_acc_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_3415_, v_keys_3416_, v_vals_3417_, v_i_3418_, v_acc_3419_);
    crate::leanh::lean_dec_ref(v_vals_3417_);
    crate::leanh::lean_dec_ref(v_keys_3416_);
    return v_res_3420_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(
    mut v_f_3421_: *mut crate::leanh::LeanObject,
    mut v_x_3422_: *mut crate::leanh::LeanObject,
    mut v_x_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3422_) == 0 {
        let mut v_es_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3427_: u8 = 0;
        v_es_3424_ = crate::leanh::lean_ctor_get(v_x_3422_, 0);
        v___x_3425_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3426_ = lean_array_get_size(v_es_3424_);
        v___x_3427_ = lean_nat_dec_lt(v___x_3425_, v___x_3426_);
        if v___x_3427_ == 0 {
            crate::leanh::lean_dec(v_f_3421_);
            return v_x_3423_;
        } else {
            let mut v___x_3428_: u8 = 0;
            v___x_3428_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
            if v___x_3428_ == 0 {
                if v___x_3427_ == 0 {
                    crate::leanh::lean_dec(v_f_3421_);
                    return v_x_3423_;
                } else {
                    let mut v___x_3429_: usize = 0;
                    let mut v___x_3430_: usize = 0;
                    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3429_ = 0usize;
                    v___x_3430_ = lean_usize_of_nat(v___x_3426_);
                    v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3421_, v_es_3424_, v___x_3429_, v___x_3430_, v_x_3423_);
                    return v___x_3431_;
                }
            } else {
                let mut v___x_3432_: usize = 0;
                let mut v___x_3433_: usize = 0;
                let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3432_ = 0usize;
                v___x_3433_ = lean_usize_of_nat(v___x_3426_);
                v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3421_, v_es_3424_, v___x_3432_, v___x_3433_, v_x_3423_);
                return v___x_3434_;
            }
        }
    } else {
        let mut v_ks_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_3435_ = crate::leanh::lean_ctor_get(v_x_3422_, 0);
        v_vs_3436_ = crate::leanh::lean_ctor_get(v_x_3422_, 1);
        v___x_3437_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_3421_, v_ks_3435_, v_vs_3436_, v___x_3437_, v_x_3423_);
        return v___x_3438_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(
    mut v_f_3439_: *mut crate::leanh::LeanObject,
    mut v_as_3440_: *mut crate::leanh::LeanObject,
    mut v_i_3441_: usize,
    mut v_stop_3442_: usize,
    mut v_b_3443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3449_ = lean_usize_dec_eq(v_i_3441_, v_stop_3442_);
                if v___x_3449_ == 0 {
                    v___x_3450_ = lean_array_uget_borrowed(v_as_3440_, v_i_3441_);
                    match crate::leanh::lean_obj_tag(v___x_3450_) {
                        0 => {
                            v_key_3451_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                            v_val_3452_ = crate::leanh::lean_ctor_get(v___x_3450_, 1);
                            crate::leanh::lean_inc(v_f_3439_);
                            crate::leanh::lean_inc(v_val_3452_);
                            crate::leanh::lean_inc(v_key_3451_);
                            v___x_3453_ = crate::leanh::lean_apply_3(
                                v_f_3439_,
                                v_b_3443_,
                                v_key_3451_,
                                v_val_3452_,
                            );
                            v___y_3445_ = v___x_3453_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3454_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                            crate::leanh::lean_inc(v_f_3439_);
                            v___x_3455_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_3439_, v_node_3454_, v_b_3443_);
                            v___y_3445_ = v___x_3455_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3445_ = v_b_3443_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_3439_);
                    return v_b_3443_;
                }
            }
            1 => {
                v___x_3446_ = 1usize;
                v___x_3447_ = lean_usize_add(v_i_3441_, v___x_3446_);
                v_i_3441_ = v___x_3447_;
                v_b_3443_ = v___y_3445_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg___boxed(
    mut v_f_3456_: *mut crate::leanh::LeanObject,
    mut v_as_3457_: *mut crate::leanh::LeanObject,
    mut v_i_3458_: *mut crate::leanh::LeanObject,
    mut v_stop_3459_: *mut crate::leanh::LeanObject,
    mut v_b_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3461_: usize = 0;
    let mut v_stop_boxed_3462_: usize = 0;
    let mut v_res_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3461_ = crate::leanh::lean_unbox_usize(v_i_3458_);
    crate::leanh::lean_dec(v_i_3458_);
    v_stop_boxed_3462_ = crate::leanh::lean_unbox_usize(v_stop_3459_);
    crate::leanh::lean_dec(v_stop_3459_);
    v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3456_, v_as_3457_, v_i_boxed_3461_, v_stop_boxed_3462_, v_b_3460_);
    crate::leanh::lean_dec_ref(v_as_3457_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg___boxed(
    mut v_f_3464_: *mut crate::leanh::LeanObject,
    mut v_x_3465_: *mut crate::leanh::LeanObject,
    mut v_x_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_3464_, v_x_3465_, v_x_3466_);
    crate::leanh::lean_dec_ref(v_x_3465_);
    return v_res_3467_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0(
    mut v_f_3468_: *mut crate::leanh::LeanObject,
    mut v_x1_3469_: *mut crate::leanh::LeanObject,
    mut v_x2_3470_: *mut crate::leanh::LeanObject,
    mut v_x3_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = crate::leanh::lean_apply_3(v_f_3468_, v_x1_3469_, v_x2_3470_, v_x3_3471_);
    return v___x_3472_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(
    mut v_map_3473_: *mut crate::leanh::LeanObject,
    mut v_f_3474_: *mut crate::leanh::LeanObject,
    mut v_init_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3476_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3476_, 0, v_f_3474_);
    v___x_3477_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v___f_3476_, v_map_3473_, v_init_3475_);
    return v___x_3477_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___boxed(
    mut v_map_3478_: *mut crate::leanh::LeanObject,
    mut v_f_3479_: *mut crate::leanh::LeanObject,
    mut v_init_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_3478_, v_f_3479_, v_init_3480_);
    crate::leanh::lean_dec_ref(v_map_3478_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0(
    mut v_ps_3482_: *mut crate::leanh::LeanObject,
    mut v_k_3483_: *mut crate::leanh::LeanObject,
    mut v_v_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3485_, 0, v_k_3483_);
    crate::leanh::lean_ctor_set(v___x_3485_, 1, v_v_3484_);
    v___x_3486_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3486_, 0, v___x_3485_);
    crate::leanh::lean_ctor_set(v___x_3486_, 1, v_ps_3482_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(
    mut v_m_3488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3489_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0;
    v___x_3490_ = crate::leanh::lean_box(0);
    v___x_3491_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_m_3488_, v___f_3489_, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___boxed(
    mut v_m_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_3492_);
    crate::leanh::lean_dec_ref(v_m_3492_);
    return v_res_3493_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0;
    v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
    return v___x_3496_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2;
    v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
    return v___x_3499_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3500_ = crate::leanh::lean_box(1);
    v___x_3501_ = l_Lean_MessageData_ofFormat(v___x_3500_);
    return v___x_3501_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3503_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5;
    v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
    return v___x_3504_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3508_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8;
    v___x_3509_ = l_Lean_MessageData_ofFormat(v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11;
    v___x_3514_ = l_Lean_MessageData_ofFormat(v___x_3513_);
    return v___x_3514_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3515_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13);
    v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14);
    v___x_3519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3519_, 0, v___x_3518_);
    crate::leanh::lean_ctor_set(v___x_3519_, 1, v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(
    mut v_a_3520_: u8,
    mut v_kind_3521_: *mut crate::leanh::LeanObject,
    mut v___x_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v___x_3524_: u8,
    mut v_diag_3525_: *mut crate::leanh::LeanObject,
    mut v___y_3526_: *mut crate::leanh::LeanObject,
    mut v___y_3527_: *mut crate::leanh::LeanObject,
    mut v___y_3528_: *mut crate::leanh::LeanObject,
    mut v___y_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: u8 = 0;
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3593_: u8 = 0;
    let mut v_inheritedTraceOptions_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v_fileName_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3611_: u8 = 0;
    let mut v_inheritedTraceOptions_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_unused_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: u8 = 0;
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v_unused_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: u8 = 0;
    let mut v___y_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_unused_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3580_ = lean_st_ref_get(v___y_3529_);
                v_fileName_3581_ = crate::leanh::lean_ctor_get(v___y_3528_, 0);
                v_fileMap_3582_ = crate::leanh::lean_ctor_get(v___y_3528_, 1);
                v_options_3583_ = crate::leanh::lean_ctor_get(v___y_3528_, 2);
                v_currRecDepth_3584_ = crate::leanh::lean_ctor_get(v___y_3528_, 3);
                v_ref_3585_ = crate::leanh::lean_ctor_get(v___y_3528_, 5);
                v_currNamespace_3586_ = crate::leanh::lean_ctor_get(v___y_3528_, 6);
                v_openDecls_3587_ = crate::leanh::lean_ctor_get(v___y_3528_, 7);
                v_initHeartbeats_3588_ = crate::leanh::lean_ctor_get(v___y_3528_, 8);
                v_maxHeartbeats_3589_ = crate::leanh::lean_ctor_get(v___y_3528_, 9);
                v_quotContext_3590_ = crate::leanh::lean_ctor_get(v___y_3528_, 10);
                v_currMacroScope_3591_ = crate::leanh::lean_ctor_get(v___y_3528_, 11);
                v_cancelTk_x3f_3592_ = crate::leanh::lean_ctor_get(v___y_3528_, 12);
                v_suppressElabErrors_3593_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3528_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3594_ = crate::leanh::lean_ctor_get(v___y_3528_, 13);
                v_env_3595_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                crate::leanh::lean_inc_ref(v_env_3595_);
                crate::leanh::lean_dec(v___x_3580_);
                v___x_3596_ = l_Lean_diagnostics;
                crate::leanh::lean_inc_ref(v_options_3583_);
                v___x_3597_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_options_3583_, v___x_3596_, v_a_3520_);
                v___x_3598_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___x_3597_, v___x_3596_);
                v___x_3674_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3595_);
                crate::leanh::lean_dec_ref(v_env_3595_);
                if v___x_3674_ == 0 {
                    if v___x_3598_ == 0 {
                        v_fileName_3600_ = v_fileName_3581_;
                        v_fileMap_3601_ = v_fileMap_3582_;
                        v_currRecDepth_3602_ = v_currRecDepth_3584_;
                        v_ref_3603_ = v_ref_3585_;
                        v_currNamespace_3604_ = v_currNamespace_3586_;
                        v_openDecls_3605_ = v_openDecls_3587_;
                        v_initHeartbeats_3606_ = v_initHeartbeats_3588_;
                        v_maxHeartbeats_3607_ = v_maxHeartbeats_3589_;
                        v_quotContext_3608_ = v_quotContext_3590_;
                        v_currMacroScope_3609_ = v_currMacroScope_3591_;
                        v_cancelTk_x3f_3610_ = v_cancelTk_x3f_3592_;
                        v_suppressElabErrors_3611_ = v_suppressElabErrors_3593_;
                        v_inheritedTraceOptions_3612_ = v_inheritedTraceOptions_3594_;
                        v___y_3613_ = v___y_3529_;
                        state = 4;
                        continue;
                    } else {
                        v___y_3653_ = v___x_3674_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_3653_ = v___x_3598_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                if v___y_3533_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3532_);
                    v___x_3534_ = crate::leanh::lean_box(0);
                    v___x_3535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3535_, 0, v___x_3534_);
                    return v___x_3535_;
                } else {
                    v___x_3536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v___y_3532_);
                    return v___x_3536_;
                }
            }
            2 => {
                v___x_3541_ = l_Lean_stringToMessageData(v_kind_3521_);
                v___x_3542_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1);
                v___x_3543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3541_);
                crate::leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                crate::leanh::lean_inc_ref(v___y_3540_);
                v___x_3544_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                crate::leanh::lean_ctor_set(v___x_3544_, 1, v___y_3540_);
                v___x_3545_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3);
                v___x_3546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3546_, 0, v___x_3544_);
                crate::leanh::lean_ctor_set(v___x_3546_, 1, v___x_3545_);
                v___x_3547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4);
                v___x_3548_ = l_Lean_MessageData_joinSep(v___y_3539_, v___x_3547_);
                v___x_3549_ = l_Lean_indentD(v___x_3548_);
                v___x_3550_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3546_);
                crate::leanh::lean_ctor_set(v___x_3550_, 1, v___x_3549_);
                v___x_3551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6);
                v___x_3552_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3550_);
                crate::leanh::lean_ctor_set(v___x_3552_, 1, v___x_3551_);
                v___x_3553_ = l_Lean_Exception_toMessageData(v___y_3538_);
                v___x_3554_ = l_Lean_indentD(v___x_3553_);
                v___x_3555_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3555_, 0, v___x_3552_);
                crate::leanh::lean_ctor_set(v___x_3555_, 1, v___x_3554_);
                v___x_3556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3556_, 0, v___x_3555_);
                v___x_3557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3557_, 0, v___x_3556_);
                return v___x_3557_;
            }
            3 => {
                if v___y_3562_ == 0 {
                    v___x_3563_ = lean_st_ref_get(v___y_3527_);
                    v___x_3564_ = lean_st_ref_get(v___y_3561_);
                    v_diag_3565_ = crate::leanh::lean_ctor_get(v___x_3563_, 4);
                    crate::leanh::lean_inc_ref(v_diag_3565_);
                    crate::leanh::lean_dec(v___x_3563_);
                    v_unfoldCounter_3566_ = crate::leanh::lean_ctor_get(v_diag_3565_, 0);
                    crate::leanh::lean_inc_ref(v_unfoldCounter_3566_);
                    crate::leanh::lean_dec_ref(v_diag_3565_);
                    v_env_3567_ = crate::leanh::lean_ctor_get(v___x_3564_, 0);
                    crate::leanh::lean_inc_ref(v_env_3567_);
                    crate::leanh::lean_dec(v___x_3564_);
                    v___x_3568_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v___y_3560_, v_unfoldCounter_3566_);
                    crate::leanh::lean_dec_ref(v___y_3560_);
                    v___x_3569_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v___x_3568_);
                    crate::leanh::lean_dec_ref(v___x_3568_);
                    v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_3522_);
                    v___x_3571_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_env_3567_, v___x_3569_, v___x_3570_);
                    v___x_3572_ = l_List_isEmpty___redArg(v___x_3571_);
                    if v___x_3572_ == 0 {
                        v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3;
                        v___x_3574_ = lean_string_dec_eq(v_kind_3521_, v___x_3573_);
                        if v___x_3574_ == 0 {
                            v___x_3575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9);
                            v___y_3538_ = v___y_3559_;
                            v___y_3539_ = v___x_3571_;
                            v___y_3540_ = v___x_3575_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12);
                            v___y_3538_ = v___y_3559_;
                            v___y_3539_ = v___x_3571_;
                            v___y_3540_ = v___x_3576_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3571_);
                        crate::leanh::lean_dec_ref(v___y_3559_);
                        crate::leanh::lean_dec_ref(v_kind_3521_);
                        v___x_3577_ = crate::leanh::lean_box(0);
                        v___x_3578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3578_, 0, v___x_3577_);
                        return v___x_3578_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3560_);
                    crate::leanh::lean_dec_ref(v_kind_3521_);
                    v___x_3579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3579_, 0, v___y_3559_);
                    return v___x_3579_;
                }
            }
            4 => {
                v___x_3614_ = l_Lean_maxRecDepth;
                v___x_3615_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v___x_3597_, v___x_3614_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3612_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3610_);
                crate::leanh::lean_inc(v_currMacroScope_3609_);
                crate::leanh::lean_inc(v_quotContext_3608_);
                crate::leanh::lean_inc(v_maxHeartbeats_3607_);
                crate::leanh::lean_inc(v_initHeartbeats_3606_);
                crate::leanh::lean_inc(v_openDecls_3605_);
                crate::leanh::lean_inc(v_currNamespace_3604_);
                crate::leanh::lean_inc(v_ref_3603_);
                crate::leanh::lean_inc(v_currRecDepth_3602_);
                crate::leanh::lean_inc_ref(v_fileMap_3601_);
                crate::leanh::lean_inc_ref(v_fileName_3600_);
                v___x_3616_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3616_, 0, v_fileName_3600_);
                crate::leanh::lean_ctor_set(v___x_3616_, 1, v_fileMap_3601_);
                crate::leanh::lean_ctor_set(v___x_3616_, 2, v___x_3597_);
                crate::leanh::lean_ctor_set(v___x_3616_, 3, v_currRecDepth_3602_);
                crate::leanh::lean_ctor_set(v___x_3616_, 4, v___x_3615_);
                crate::leanh::lean_ctor_set(v___x_3616_, 5, v_ref_3603_);
                crate::leanh::lean_ctor_set(v___x_3616_, 6, v_currNamespace_3604_);
                crate::leanh::lean_ctor_set(v___x_3616_, 7, v_openDecls_3605_);
                crate::leanh::lean_ctor_set(v___x_3616_, 8, v_initHeartbeats_3606_);
                crate::leanh::lean_ctor_set(v___x_3616_, 9, v_maxHeartbeats_3607_);
                crate::leanh::lean_ctor_set(v___x_3616_, 10, v_quotContext_3608_);
                crate::leanh::lean_ctor_set(v___x_3616_, 11, v_currMacroScope_3609_);
                crate::leanh::lean_ctor_set(v___x_3616_, 12, v_cancelTk_x3f_3610_);
                crate::leanh::lean_ctor_set(v___x_3616_, 13, v_inheritedTraceOptions_3612_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3616_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___x_3598_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3616_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3611_,
                );
                crate::leanh::lean_inc_ref(v_a_3523_);
                v___x_3617_ = l_Lean_Meta_check(
                    v_a_3523_,
                    v___x_3524_,
                    v___y_3526_,
                    v___y_3527_,
                    v___x_3616_,
                    v___y_3613_,
                );
                if crate::leanh::lean_obj_tag(v___x_3617_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3617_, 1);
                    v___x_3618_ = lean_st_ref_get(v___y_3527_);
                    v___x_3619_ = lean_st_ref_take(v___y_3527_);
                    v_mctx_3620_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
                    v_cache_3621_ = crate::leanh::lean_ctor_get(v___x_3619_, 1);
                    v_zetaDeltaFVarIds_3622_ = crate::leanh::lean_ctor_get(v___x_3619_, 2);
                    v_postponed_3623_ = crate::leanh::lean_ctor_get(v___x_3619_, 3);
                    v_isSharedCheck_3647_ = (!crate::leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3647_ == 0 {
                        v_unused_3648_ = crate::leanh::lean_ctor_get(v___x_3619_, 4);
                        crate::leanh::lean_dec(v_unused_3648_);
                        v___x_3625_ = v___x_3619_;
                        v_isShared_3626_ = v_isSharedCheck_3647_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_postponed_3623_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3622_);
                        crate::leanh::lean_inc(v_cache_3621_);
                        crate::leanh::lean_inc(v_mctx_3620_);
                        crate::leanh::lean_dec(v___x_3619_);
                        v___x_3625_ = crate::leanh::lean_box(0);
                        v_isShared_3626_ = v_isSharedCheck_3647_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3616_, 14);
                    crate::leanh::lean_dec_ref(v_diag_3525_);
                    crate::leanh::lean_dec_ref(v_a_3523_);
                    crate::leanh::lean_dec_ref(v_kind_3521_);
                    v_a_3649_ = crate::leanh::lean_ctor_get(v___x_3617_, 0);
                    crate::leanh::lean_inc(v_a_3649_);
                    crate::leanh::lean_dec_ref_known(v___x_3617_, 1);
                    v___x_3650_ = l_Lean_Exception_isInterrupt(v_a_3649_);
                    if v___x_3650_ == 0 {
                        crate::leanh::lean_inc(v_a_3649_);
                        v___x_3651_ = l_Lean_Exception_isRuntime(v_a_3649_);
                        v___y_3532_ = v_a_3649_;
                        v___y_3533_ = v___x_3651_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3532_ = v_a_3649_;
                        v___y_3533_ = v___x_3650_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3625_, 4, v_diag_3525_);
                    v___x_3628_ = v___x_3625_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_mctx_3620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_cache_3621_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3646_,
                        2,
                        v_zetaDeltaFVarIds_3622_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 3, v_postponed_3623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 4, v_diag_3525_);
                    v___x_3628_ = v_reuseFailAlloc_3646_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3629_ = lean_st_ref_set(v___y_3527_, v___x_3628_);
                v___x_3630_ = 3;
                v___x_3631_ = l_Lean_Meta_check(
                    v_a_3523_,
                    v___x_3630_,
                    v___y_3526_,
                    v___y_3527_,
                    v___x_3616_,
                    v___y_3613_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3616_, 14);
                if crate::leanh::lean_obj_tag(v___x_3631_) == 0 {
                    crate::leanh::lean_dec(v___x_3618_);
                    crate::leanh::lean_dec_ref(v_kind_3521_);
                    v_isSharedCheck_3639_ = (!crate::leanh::lean_is_exclusive(v___x_3631_)) as u8;
                    if v_isSharedCheck_3639_ == 0 {
                        v_unused_3640_ = crate::leanh::lean_ctor_get(v___x_3631_, 0);
                        crate::leanh::lean_dec(v_unused_3640_);
                        v___x_3633_ = v___x_3631_;
                        v_isShared_3634_ = v_isSharedCheck_3639_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3631_);
                        v___x_3633_ = crate::leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3639_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_diag_3641_ = crate::leanh::lean_ctor_get(v___x_3618_, 4);
                    crate::leanh::lean_inc_ref(v_diag_3641_);
                    crate::leanh::lean_dec(v___x_3618_);
                    v_a_3642_ = crate::leanh::lean_ctor_get(v___x_3631_, 0);
                    crate::leanh::lean_inc(v_a_3642_);
                    crate::leanh::lean_dec_ref_known(v___x_3631_, 1);
                    v_unfoldCounter_3643_ = crate::leanh::lean_ctor_get(v_diag_3641_, 0);
                    crate::leanh::lean_inc_ref(v_unfoldCounter_3643_);
                    crate::leanh::lean_dec_ref(v_diag_3641_);
                    v___x_3644_ = l_Lean_Exception_isInterrupt(v_a_3642_);
                    if v___x_3644_ == 0 {
                        crate::leanh::lean_inc(v_a_3642_);
                        v___x_3645_ = l_Lean_Exception_isRuntime(v_a_3642_);
                        v___y_3559_ = v_a_3642_;
                        v___y_3560_ = v_unfoldCounter_3643_;
                        v___y_3561_ = v___y_3613_;
                        v___y_3562_ = v___x_3645_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3559_ = v_a_3642_;
                        v___y_3560_ = v_unfoldCounter_3643_;
                        v___y_3561_ = v___y_3613_;
                        v___y_3562_ = v___x_3644_;
                        state = 3;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3635_ = crate::leanh::lean_box(0);
                if v_isShared_3634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3633_, 0, v___x_3635_);
                    v___x_3637_ = v___x_3633_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
                    v___x_3637_ = v_reuseFailAlloc_3638_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3637_;
            }
            9 => {
                if v___y_3653_ == 0 {
                    v___x_3654_ = lean_st_ref_take(v___y_3529_);
                    v_env_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                    v_nextMacroScope_3656_ = crate::leanh::lean_ctor_get(v___x_3654_, 1);
                    v_ngen_3657_ = crate::leanh::lean_ctor_get(v___x_3654_, 2);
                    v_auxDeclNGen_3658_ = crate::leanh::lean_ctor_get(v___x_3654_, 3);
                    v_traceState_3659_ = crate::leanh::lean_ctor_get(v___x_3654_, 4);
                    v_messages_3660_ = crate::leanh::lean_ctor_get(v___x_3654_, 6);
                    v_infoState_3661_ = crate::leanh::lean_ctor_get(v___x_3654_, 7);
                    v_snapshotTasks_3662_ = crate::leanh::lean_ctor_get(v___x_3654_, 8);
                    v_isSharedCheck_3672_ = (!crate::leanh::lean_is_exclusive(v___x_3654_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v_unused_3673_ = crate::leanh::lean_ctor_get(v___x_3654_, 5);
                        crate::leanh::lean_dec(v_unused_3673_);
                        v___x_3664_ = v___x_3654_;
                        v_isShared_3665_ = v_isSharedCheck_3672_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_3662_);
                        crate::leanh::lean_inc(v_infoState_3661_);
                        crate::leanh::lean_inc(v_messages_3660_);
                        crate::leanh::lean_inc(v_traceState_3659_);
                        crate::leanh::lean_inc(v_auxDeclNGen_3658_);
                        crate::leanh::lean_inc(v_ngen_3657_);
                        crate::leanh::lean_inc(v_nextMacroScope_3656_);
                        crate::leanh::lean_inc(v_env_3655_);
                        crate::leanh::lean_dec(v___x_3654_);
                        v___x_3664_ = crate::leanh::lean_box(0);
                        v_isShared_3665_ = v_isSharedCheck_3672_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_fileName_3600_ = v_fileName_3581_;
                    v_fileMap_3601_ = v_fileMap_3582_;
                    v_currRecDepth_3602_ = v_currRecDepth_3584_;
                    v_ref_3603_ = v_ref_3585_;
                    v_currNamespace_3604_ = v_currNamespace_3586_;
                    v_openDecls_3605_ = v_openDecls_3587_;
                    v_initHeartbeats_3606_ = v_initHeartbeats_3588_;
                    v_maxHeartbeats_3607_ = v_maxHeartbeats_3589_;
                    v_quotContext_3608_ = v_quotContext_3590_;
                    v_currMacroScope_3609_ = v_currMacroScope_3591_;
                    v_cancelTk_x3f_3610_ = v_cancelTk_x3f_3592_;
                    v_suppressElabErrors_3611_ = v_suppressElabErrors_3593_;
                    v_inheritedTraceOptions_3612_ = v_inheritedTraceOptions_3594_;
                    v___y_3613_ = v___y_3529_;
                    state = 4;
                    continue;
                }
            }
            10 => {
                v___x_3666_ = l_Lean_Kernel_enableDiag(v_env_3655_, v___x_3598_);
                v___x_3667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15);
                if v_isShared_3665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3664_, 5, v___x_3667_);
                    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3666_);
                    v___x_3669_ = v___x_3664_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_nextMacroScope_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_ngen_3657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_auxDeclNGen_3658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 4, v_traceState_3659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 5, v___x_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 6, v_messages_3660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 7, v_infoState_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 8, v_snapshotTasks_3662_);
                    v___x_3669_ = v_reuseFailAlloc_3671_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3670_ = lean_st_ref_set(v___y_3529_, v___x_3669_);
                v_fileName_3600_ = v_fileName_3581_;
                v_fileMap_3601_ = v_fileMap_3582_;
                v_currRecDepth_3602_ = v_currRecDepth_3584_;
                v_ref_3603_ = v_ref_3585_;
                v_currNamespace_3604_ = v_currNamespace_3586_;
                v_openDecls_3605_ = v_openDecls_3587_;
                v_initHeartbeats_3606_ = v_initHeartbeats_3588_;
                v_maxHeartbeats_3607_ = v_maxHeartbeats_3589_;
                v_quotContext_3608_ = v_quotContext_3590_;
                v_currMacroScope_3609_ = v_currMacroScope_3591_;
                v_cancelTk_x3f_3610_ = v_cancelTk_x3f_3592_;
                v_suppressElabErrors_3611_ = v_suppressElabErrors_3593_;
                v_inheritedTraceOptions_3612_ = v_inheritedTraceOptions_3594_;
                v___y_3613_ = v___y_3529_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed(
    mut v_a_3675_: *mut crate::leanh::LeanObject,
    mut v_kind_3676_: *mut crate::leanh::LeanObject,
    mut v___x_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v___x_3679_: *mut crate::leanh::LeanObject,
    mut v_diag_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_30843__boxed_3686_: u8 = 0;
    let mut v___x_30846__boxed_3687_: u8 = 0;
    let mut v_res_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_30843__boxed_3686_ = (crate::leanh::lean_unbox(v_a_3675_) as u8);
    v___x_30846__boxed_3687_ = (crate::leanh::lean_unbox(v___x_3679_) as u8);
    v_res_3688_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(v_a_30843__boxed_3686_, v_kind_3676_, v___x_3677_, v_a_3678_, v___x_30846__boxed_3687_, v_diag_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    crate::leanh::lean_dec(v___y_3684_);
    crate::leanh::lean_dec_ref(v___y_3683_);
    crate::leanh::lean_dec(v___y_3682_);
    crate::leanh::lean_dec_ref(v___y_3681_);
    crate::leanh::lean_dec(v___x_3677_);
    return v_res_3688_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(
    mut v_a_3694_: u8,
    mut v_kind_3695_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3696_: *mut crate::leanh::LeanObject,
    mut v_b_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
    mut v___y_3700_: *mut crate::leanh::LeanObject,
    mut v___y_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut v_unused_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3696_) == 0 {
                    crate::leanh::lean_dec_ref(v_kind_3695_);
                    v___x_3703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3703_, 0, v_b_3697_);
                    return v___x_3703_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3697_);
                    v_head_3704_ = crate::leanh::lean_ctor_get(v_as_x27_3696_, 0);
                    v_tail_3705_ = crate::leanh::lean_ctor_get(v_as_x27_3696_, 1);
                    v___x_3706_ = lean_st_ref_get(v___y_3699_);
                    v_mctx_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3707_);
                    crate::leanh::lean_dec(v___x_3706_);
                    v___x_3708_ = crate::leanh::lean_box(0);
                    v___x_3709_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0;
                    v___x_3716_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_3707_, v_head_3704_);
                    crate::leanh::lean_dec_ref(v_mctx_3707_);
                    if crate::leanh::lean_obj_tag(v___x_3716_) == 1 {
                        v_val_3717_ = crate::leanh::lean_ctor_get(v___x_3716_, 0);
                        crate::leanh::lean_inc(v_val_3717_);
                        crate::leanh::lean_dec_ref_known(v___x_3716_, 1);
                        v_lctx_3718_ = crate::leanh::lean_ctor_get(v_val_3717_, 1);
                        crate::leanh::lean_inc_ref(v_lctx_3718_);
                        v_type_3719_ = crate::leanh::lean_ctor_get(v_val_3717_, 2);
                        crate::leanh::lean_inc_ref(v_type_3719_);
                        crate::leanh::lean_dec(v_val_3717_);
                        v___x_3720_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_3719_, v___y_3699_);
                        v_a_3721_ = crate::leanh::lean_ctor_get(v___x_3720_, 0);
                        crate::leanh::lean_inc(v_a_3721_);
                        crate::leanh::lean_dec_ref(v___x_3720_);
                        v___x_3722_ = lean_st_ref_get(v___y_3699_);
                        v_diag_3723_ = crate::leanh::lean_ctor_get(v___x_3722_, 4);
                        crate::leanh::lean_inc_ref_n(v_diag_3723_, 2);
                        crate::leanh::lean_dec(v___x_3722_);
                        v___x_3724_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3725_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1;
                        v___x_3726_ = 1;
                        v___x_3727_ = crate::leanh::lean_box((v_a_3694_) as usize);
                        v___x_3728_ = crate::leanh::lean_box((v___x_3726_) as usize);
                        crate::leanh::lean_inc_ref(v_kind_3695_);
                        v___f_3729_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                        crate::leanh::lean_closure_set(v___f_3729_, 0, v___x_3727_);
                        crate::leanh::lean_closure_set(v___f_3729_, 1, v_kind_3695_);
                        crate::leanh::lean_closure_set(v___f_3729_, 2, v___x_3724_);
                        crate::leanh::lean_closure_set(v___f_3729_, 3, v_a_3721_);
                        crate::leanh::lean_closure_set(v___f_3729_, 4, v___x_3728_);
                        crate::leanh::lean_closure_set(v___f_3729_, 5, v_diag_3723_);
                        v___x_3730_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_3718_, v___x_3725_, v___f_3729_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
                        if crate::leanh::lean_obj_tag(v___x_3730_) == 0 {
                            v_a_3731_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                            crate::leanh::lean_inc(v_a_3731_);
                            crate::leanh::lean_dec_ref_known(v___x_3730_, 1);
                            v___x_3732_ = lean_st_ref_take(v___y_3699_);
                            v_mctx_3733_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                            v_cache_3734_ = crate::leanh::lean_ctor_get(v___x_3732_, 1);
                            v_zetaDeltaFVarIds_3735_ = crate::leanh::lean_ctor_get(v___x_3732_, 2);
                            v_postponed_3736_ = crate::leanh::lean_ctor_get(v___x_3732_, 3);
                            v_isSharedCheck_3744_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3732_)) as u8;
                            if v_isSharedCheck_3744_ == 0 {
                                v_unused_3745_ = crate::leanh::lean_ctor_get(v___x_3732_, 4);
                                crate::leanh::lean_dec(v_unused_3745_);
                                v___x_3738_ = v___x_3732_;
                                v_isShared_3739_ = v_isSharedCheck_3744_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_postponed_3736_);
                                crate::leanh::lean_inc(v_zetaDeltaFVarIds_3735_);
                                crate::leanh::lean_inc(v_cache_3734_);
                                crate::leanh::lean_inc(v_mctx_3733_);
                                crate::leanh::lean_dec(v___x_3732_);
                                v___x_3738_ = crate::leanh::lean_box(0);
                                v_isShared_3739_ = v_isSharedCheck_3744_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_diag_3723_);
                            if crate::leanh::lean_obj_tag(v___x_3730_) == 0 {
                                v_a_3746_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                                crate::leanh::lean_inc(v_a_3746_);
                                crate::leanh::lean_dec_ref_known(v___x_3730_, 1);
                                v_a_3711_ = v_a_3746_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_kind_3695_);
                                v_a_3747_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                                v_isSharedCheck_3754_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3730_)) as u8;
                                if v_isSharedCheck_3754_ == 0 {
                                    v___x_3749_ = v___x_3730_;
                                    v_isShared_3750_ = v_isSharedCheck_3754_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3747_);
                                    crate::leanh::lean_dec(v___x_3730_);
                                    v___x_3749_ = crate::leanh::lean_box(0);
                                    v_isShared_3750_ = v_isSharedCheck_3754_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3716_);
                        v_as_x27_3696_ = v_tail_3705_;
                        v_b_3697_ = v___x_3709_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3711_) == 1 {
                    crate::leanh::lean_dec_ref(v_kind_3695_);
                    v___x_3712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3712_, 0, v_a_3711_);
                    v___x_3713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3713_, 0, v___x_3712_);
                    crate::leanh::lean_ctor_set(v___x_3713_, 1, v___x_3708_);
                    v___x_3714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3714_, 0, v___x_3713_);
                    return v___x_3714_;
                } else {
                    crate::leanh::lean_dec(v_a_3711_);
                    v_as_x27_3696_ = v_tail_3705_;
                    v_b_3697_ = v___x_3709_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_3739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3738_, 4, v_diag_3723_);
                    v___x_3741_ = v___x_3738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3743_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_mctx_3733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_cache_3734_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3743_,
                        2,
                        v_zetaDeltaFVarIds_3735_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_postponed_3736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 4, v_diag_3723_);
                    v___x_3741_ = v_reuseFailAlloc_3743_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3742_ = lean_st_ref_set(v___y_3699_, v___x_3741_);
                v_a_3711_ = v_a_3731_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3750_ == 0 {
                    v___x_3752_ = v___x_3749_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3753_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___boxed(
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_kind_3757_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3758_: *mut crate::leanh::LeanObject,
    mut v_b_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_31106__boxed_3765_: u8 = 0;
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_31106__boxed_3765_ = (crate::leanh::lean_unbox(v_a_3756_) as u8);
    v_res_3766_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_31106__boxed_3765_, v_kind_3757_, v_as_x27_3758_, v_b_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
    crate::leanh::lean_dec(v___y_3763_);
    crate::leanh::lean_dec_ref(v___y_3762_);
    crate::leanh::lean_dec(v___y_3761_);
    crate::leanh::lean_dec_ref(v___y_3760_);
    crate::leanh::lean_dec(v_as_x27_3758_);
    return v_res_3766_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(
    mut v_a_3767_: u8,
    mut v_kind_3768_: *mut crate::leanh::LeanObject,
    mut v_goals_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
    mut v___y_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v_fst_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_a_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3775_ = crate::leanh::lean_box(0);
                v___x_3776_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0;
                v___x_3777_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_3767_, v_kind_3768_, v_goals_3769_, v___x_3776_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
                if crate::leanh::lean_obj_tag(v___x_3777_) == 0 {
                    v_a_3778_ = crate::leanh::lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3790_ = (!crate::leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3780_ = v___x_3777_;
                        v_isShared_3781_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3778_);
                        crate::leanh::lean_dec(v___x_3777_);
                        v___x_3780_ = crate::leanh::lean_box(0);
                        v_isShared_3781_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3791_ = crate::leanh::lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3798_ = (!crate::leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3798_ == 0 {
                        v___x_3793_ = v___x_3777_;
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3791_);
                        crate::leanh::lean_dec(v___x_3777_);
                        v___x_3793_ = crate::leanh::lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3782_ = crate::leanh::lean_ctor_get(v_a_3778_, 0);
                crate::leanh::lean_inc(v_fst_3782_);
                crate::leanh::lean_dec(v_a_3778_);
                if crate::leanh::lean_obj_tag(v_fst_3782_) == 0 {
                    if v_isShared_3781_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3780_, 0, v___x_3775_);
                        v___x_3784_ = v___x_3780_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3775_);
                        v___x_3784_ = v_reuseFailAlloc_3785_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3786_ = crate::leanh::lean_ctor_get(v_fst_3782_, 0);
                    crate::leanh::lean_inc(v_val_3786_);
                    crate::leanh::lean_dec_ref_known(v_fst_3782_, 1);
                    if v_isShared_3781_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3780_, 0, v_val_3786_);
                        v___x_3788_ = v___x_3780_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_val_3786_);
                        v___x_3788_ = v_reuseFailAlloc_3789_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3784_;
            }
            3 => {
                return v___x_3788_;
            }
            4 => {
                if v_isShared_3794_ == 0 {
                    v___x_3796_ = v___x_3793_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
                    v___x_3796_ = v_reuseFailAlloc_3797_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed(
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_kind_3800_: *mut crate::leanh::LeanObject,
    mut v_goals_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_31224__boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_31224__boxed_3807_ = (crate::leanh::lean_unbox(v_a_3799_) as u8);
    v_res_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(v_a_31224__boxed_3807_, v_kind_3800_, v_goals_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
    crate::leanh::lean_dec(v___y_3805_);
    crate::leanh::lean_dec_ref(v___y_3804_);
    crate::leanh::lean_dec(v___y_3803_);
    crate::leanh::lean_dec_ref(v___y_3802_);
    crate::leanh::lean_dec(v_goals_3801_);
    return v_res_3808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(
    mut v_a_3809_: u8,
    mut v_val_3810_: *mut crate::leanh::LeanObject,
    mut v_as_3811_: *mut crate::leanh::LeanObject,
    mut v_sz_3812_: usize,
    mut v_i_3813_: usize,
    mut v_b_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3818_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
                if v___x_3818_ == 0 {
                    crate::leanh::lean_dec(v_val_3810_);
                    v___x_3819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3819_, 0, v_b_3814_);
                    return v___x_3819_;
                } else {
                    v___x_3820_ = crate::leanh::lean_box((v_a_3809_) as usize);
                    v___f_3821_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___f_3821_, 0, v___x_3820_);
                    v___x_3822_ = crate::leanh::lean_box((v_a_3809_) as usize);
                    v___f_3823_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_3823_, 0, v___x_3822_);
                    v___x_3824_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
                    v___x_3825_ = crate::leanh::lean_box((v_a_3809_) as usize);
                    crate::leanh::lean_inc(v_val_3810_);
                    v___f_3826_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed as *mut core::ffi::c_void, 10, 4);
                    crate::leanh::lean_closure_set(v___f_3826_, 0, v_val_3810_);
                    crate::leanh::lean_closure_set(v___f_3826_, 1, v___x_3825_);
                    crate::leanh::lean_closure_set(v___f_3826_, 2, v___x_3824_);
                    crate::leanh::lean_closure_set(v___f_3826_, 3, v___f_3821_);
                    v_a_3827_ = lean_array_uget_borrowed(v_as_3811_, v_i_3813_);
                    v___x_3828_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_3827_);
                    v___x_3829_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___f_3823_, v___f_3826_, v___x_3828_, v_a_3827_, v___y_3815_, v___y_3816_);
                    if crate::leanh::lean_obj_tag(v___x_3829_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3829_, 1);
                        v___x_3830_ = crate::leanh::lean_box(0);
                        v___x_3831_ = 1usize;
                        v___x_3832_ = lean_usize_add(v_i_3813_, v___x_3831_);
                        v_i_3813_ = v___x_3832_;
                        v_b_3814_ = v___x_3830_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_3810_);
                        return v___x_3829_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_val_3835_: *mut crate::leanh::LeanObject,
    mut v_as_3836_: *mut crate::leanh::LeanObject,
    mut v_sz_3837_: *mut crate::leanh::LeanObject,
    mut v_i_3838_: *mut crate::leanh::LeanObject,
    mut v_b_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_31289__boxed_3843_: u8 = 0;
    let mut v_sz_boxed_3844_: usize = 0;
    let mut v_i_boxed_3845_: usize = 0;
    let mut v_res_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_31289__boxed_3843_ = (crate::leanh::lean_unbox(v_a_3834_) as u8);
    v_sz_boxed_3844_ = crate::leanh::lean_unbox_usize(v_sz_3837_);
    crate::leanh::lean_dec(v_sz_3837_);
    v_i_boxed_3845_ = crate::leanh::lean_unbox_usize(v_i_3838_);
    crate::leanh::lean_dec(v_i_3838_);
    v_res_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v_a_31289__boxed_3843_, v_val_3835_, v_as_3836_, v_sz_boxed_3844_, v_i_boxed_3845_, v_b_3839_, v___y_3840_, v___y_3841_);
    crate::leanh::lean_dec(v___y_3841_);
    crate::leanh::lean_dec_ref(v___y_3840_);
    crate::leanh::lean_dec_ref(v_as_3836_);
    return v_res_3846_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(
    mut v___cmdStx_3847_: *mut crate::leanh::LeanObject,
    mut v___y_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3856_: u8 = 0;
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3870_: usize = 0;
    let mut v___x_3871_: usize = 0;
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_unused_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3851_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
                v___x_3852_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_3851_, v___y_3849_);
                v_a_3853_ = crate::leanh::lean_ctor_get(v___x_3852_, 0);
                v_isSharedCheck_3882_ = (!crate::leanh::lean_is_exclusive(v___x_3852_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v___x_3855_ = v___x_3852_;
                    v_isShared_3856_ = v_isSharedCheck_3882_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3853_);
                    crate::leanh::lean_dec(v___x_3852_);
                    v___x_3855_ = crate::leanh::lean_box(0);
                    v_isShared_3856_ = v_isSharedCheck_3882_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3857_ = (crate::leanh::lean_unbox(v_a_3853_) as u8);
                if v___x_3857_ == 0 {
                    crate::leanh::lean_dec(v_a_3853_);
                    v___x_3858_ = crate::leanh::lean_box(0);
                    if v_isShared_3856_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3855_, 0, v___x_3858_);
                        v___x_3860_ = v___x_3855_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
                        v___x_3860_ = v_reuseFailAlloc_3861_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3855_);
                    v___x_3862_ = lean_st_ref_get(v___y_3849_);
                    v___x_3863_ = 0;
                    v___x_3864_ = crate::leanh::lean_box((v___x_3863_) as usize);
                    v___x_3865_ = lean_st_mk_ref(v___x_3864_);
                    v_infoState_3866_ = crate::leanh::lean_ctor_get(v___x_3862_, 8);
                    crate::leanh::lean_inc_ref(v_infoState_3866_);
                    crate::leanh::lean_dec(v___x_3862_);
                    v_trees_3867_ = crate::leanh::lean_ctor_get(v_infoState_3866_, 2);
                    crate::leanh::lean_inc_ref(v_trees_3867_);
                    crate::leanh::lean_dec_ref(v_infoState_3866_);
                    v___x_3868_ = l_Lean_PersistentArray_toArray___redArg(v_trees_3867_);
                    crate::leanh::lean_dec_ref(v_trees_3867_);
                    v___x_3869_ = crate::leanh::lean_box(0);
                    v_sz_3870_ = lean_array_size(v___x_3868_);
                    v___x_3871_ = 0usize;
                    v___x_3872_ = (crate::leanh::lean_unbox(v_a_3853_) as u8);
                    crate::leanh::lean_dec(v_a_3853_);
                    v___x_3873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v___x_3872_, v___x_3865_, v___x_3868_, v_sz_3870_, v___x_3871_, v___x_3869_, v___y_3848_, v___y_3849_);
                    crate::leanh::lean_dec_ref(v___x_3868_);
                    if crate::leanh::lean_obj_tag(v___x_3873_) == 0 {
                        v_isSharedCheck_3880_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3873_)) as u8;
                        if v_isSharedCheck_3880_ == 0 {
                            v_unused_3881_ = crate::leanh::lean_ctor_get(v___x_3873_, 0);
                            crate::leanh::lean_dec(v_unused_3881_);
                            v___x_3875_ = v___x_3873_;
                            v_isShared_3876_ = v_isSharedCheck_3880_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3873_);
                            v___x_3875_ = crate::leanh::lean_box(0);
                            v_isShared_3876_ = v_isSharedCheck_3880_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_3873_;
                    }
                }
            }
            2 => {
                return v___x_3860_;
            }
            3 => {
                if v_isShared_3876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3875_, 0, v___x_3869_);
                    v___x_3878_ = v___x_3875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3869_);
                    v___x_3878_ = v_reuseFailAlloc_3879_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(
    mut v___cmdStx_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ =
        l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(
            v___cmdStx_3883_,
            v___y_3884_,
            v___y_3885_,
        );
    crate::leanh::lean_dec(v___y_3885_);
    crate::leanh::lean_dec_ref(v___y_3884_);
    crate::leanh::lean_dec(v___cmdStx_3883_);
    return v_res_3887_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(
    mut v_opt_3896_: *mut crate::leanh::LeanObject,
    mut v___y_3897_: *mut crate::leanh::LeanObject,
    mut v___y_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_3896_, v___y_3898_);
    return v___x_3900_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(
    mut v_opt_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3905_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_3901_, v___y_3902_, v___y_3903_);
    crate::leanh::lean_dec(v___y_3903_);
    crate::leanh::lean_dec_ref(v___y_3902_);
    crate::leanh::lean_dec_ref(v_opt_3901_);
    return v_res_3905_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(
    mut v_00_u03b2_3906_: *mut crate::leanh::LeanObject,
    mut v_m_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3908_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_3907_);
    return v___x_3908_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(
    mut v_00_u03b2_3909_: *mut crate::leanh::LeanObject,
    mut v_m_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3911_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_00_u03b2_3909_, v_m_3910_);
    crate::leanh::lean_dec_ref(v_m_3910_);
    return v_res_3911_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(
    mut v_a_3912_: u8,
    mut v_kind_3913_: *mut crate::leanh::LeanObject,
    mut v_as_3914_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3915_: *mut crate::leanh::LeanObject,
    mut v_b_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_3912_, v_kind_3913_, v_as_x27_3915_, v_b_3916_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
    return v___x_3923_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_kind_3925_: *mut crate::leanh::LeanObject,
    mut v_as_3926_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3927_: *mut crate::leanh::LeanObject,
    mut v_b_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_31468__boxed_3935_: u8 = 0;
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_31468__boxed_3935_ = (crate::leanh::lean_unbox(v_a_3924_) as u8);
    v_res_3936_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_a_31468__boxed_3935_, v_kind_3925_, v_as_3926_, v_as_x27_3927_, v_b_3928_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
    crate::leanh::lean_dec(v___y_3933_);
    crate::leanh::lean_dec_ref(v___y_3932_);
    crate::leanh::lean_dec(v___y_3931_);
    crate::leanh::lean_dec_ref(v___y_3930_);
    crate::leanh::lean_dec(v_as_x27_3927_);
    crate::leanh::lean_dec(v_as_3926_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(
    mut v_00_u03b2_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
    mut v_x_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3940_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_3938_, v_x_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(
    mut v_00_u03b2_3941_: *mut crate::leanh::LeanObject,
    mut v_x_3942_: *mut crate::leanh::LeanObject,
    mut v_x_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(v_00_u03b2_3941_, v_x_3942_, v_x_3943_);
    crate::leanh::lean_dec(v_x_3943_);
    crate::leanh::lean_dec_ref(v_x_3942_);
    return v_res_3944_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(
    mut v_00_u03b2_3945_: *mut crate::leanh::LeanObject,
    mut v_x_3946_: *mut crate::leanh::LeanObject,
    mut v_x_3947_: *mut crate::leanh::LeanObject,
    mut v_x_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_x_3946_, v_x_3947_, v_x_3948_);
    return v___x_3949_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(
    mut v_00_u03c3_3950_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3951_: *mut crate::leanh::LeanObject,
    mut v_map_3952_: *mut crate::leanh::LeanObject,
    mut v_init_3953_: *mut crate::leanh::LeanObject,
    mut v_f_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_3952_, v_init_3953_, v_f_3954_);
    return v___x_3955_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(
    mut v_00_u03c3_3956_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3957_: *mut crate::leanh::LeanObject,
    mut v_map_3958_: *mut crate::leanh::LeanObject,
    mut v_init_3959_: *mut crate::leanh::LeanObject,
    mut v_f_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(v_00_u03c3_3956_, v_00_u03b2_3957_, v_map_3958_, v_init_3959_, v_f_3960_);
    crate::leanh::lean_dec_ref(v_map_3958_);
    return v_res_3961_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(
    mut v_00_u03c3_3962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3963_: *mut crate::leanh::LeanObject,
    mut v_map_3964_: *mut crate::leanh::LeanObject,
    mut v_f_3965_: *mut crate::leanh::LeanObject,
    mut v_init_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_3964_, v_f_3965_, v_init_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(
    mut v_00_u03c3_3968_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3969_: *mut crate::leanh::LeanObject,
    mut v_map_3970_: *mut crate::leanh::LeanObject,
    mut v_f_3971_: *mut crate::leanh::LeanObject,
    mut v_init_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(v_00_u03c3_3968_, v_00_u03b2_3969_, v_map_3970_, v_f_3971_, v_init_3972_);
    crate::leanh::lean_dec_ref(v_map_3970_);
    return v_res_3973_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(
    mut v_00_u03b1_3974_: *mut crate::leanh::LeanObject,
    mut v_msg_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_3975_, v___y_3976_, v___y_3977_);
    return v___x_3979_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(
    mut v_00_u03b1_3980_: *mut crate::leanh::LeanObject,
    mut v_msg_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(v_00_u03b1_3980_, v_msg_3981_, v___y_3982_, v___y_3983_);
    crate::leanh::lean_dec(v___y_3983_);
    crate::leanh::lean_dec_ref(v___y_3982_);
    return v_res_3985_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(
    mut v_00_u03b1_3986_: *mut crate::leanh::LeanObject,
    mut v_preNode_3987_: *mut crate::leanh::LeanObject,
    mut v_postNode_3988_: *mut crate::leanh::LeanObject,
    mut v_x_3989_: *mut crate::leanh::LeanObject,
    mut v_x_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_3987_, v_postNode_3988_, v_x_3989_, v_x_3990_, v___y_3991_, v___y_3992_);
    return v___x_3994_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(
    mut v_00_u03b1_3995_: *mut crate::leanh::LeanObject,
    mut v_preNode_3996_: *mut crate::leanh::LeanObject,
    mut v_postNode_3997_: *mut crate::leanh::LeanObject,
    mut v_x_3998_: *mut crate::leanh::LeanObject,
    mut v_x_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(v_00_u03b1_3995_, v_preNode_3996_, v_postNode_3997_, v_x_3998_, v_x_3999_, v___y_4000_, v___y_4001_);
    crate::leanh::lean_dec(v___y_4001_);
    crate::leanh::lean_dec_ref(v___y_4000_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(
    mut v_00_u03b2_4004_: *mut crate::leanh::LeanObject,
    mut v_x_4005_: *mut crate::leanh::LeanObject,
    mut v_x_4006_: usize,
    mut v_x_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_4005_, v_x_4006_, v_x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(
    mut v_00_u03b2_4009_: *mut crate::leanh::LeanObject,
    mut v_x_4010_: *mut crate::leanh::LeanObject,
    mut v_x_4011_: *mut crate::leanh::LeanObject,
    mut v_x_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_31540__boxed_4013_: usize = 0;
    let mut v_res_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_31540__boxed_4013_ = crate::leanh::lean_unbox_usize(v_x_4011_);
    crate::leanh::lean_dec(v_x_4011_);
    v_res_4014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(v_00_u03b2_4009_, v_x_4010_, v_x_31540__boxed_4013_, v_x_4012_);
    crate::leanh::lean_dec(v_x_4012_);
    crate::leanh::lean_dec_ref(v_x_4010_);
    return v_res_4014_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(
    mut v_00_u03b2_4015_: *mut crate::leanh::LeanObject,
    mut v_x_4016_: *mut crate::leanh::LeanObject,
    mut v_x_4017_: usize,
    mut v_x_4018_: usize,
    mut v_x_4019_: *mut crate::leanh::LeanObject,
    mut v_x_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_4016_, v_x_4017_, v_x_4018_, v_x_4019_, v_x_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(
    mut v_00_u03b2_4022_: *mut crate::leanh::LeanObject,
    mut v_x_4023_: *mut crate::leanh::LeanObject,
    mut v_x_4024_: *mut crate::leanh::LeanObject,
    mut v_x_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_31551__boxed_4028_: usize = 0;
    let mut v_x_31552__boxed_4029_: usize = 0;
    let mut v_res_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_31551__boxed_4028_ = crate::leanh::lean_unbox_usize(v_x_4024_);
    crate::leanh::lean_dec(v_x_4024_);
    v_x_31552__boxed_4029_ = crate::leanh::lean_unbox_usize(v_x_4025_);
    crate::leanh::lean_dec(v_x_4025_);
    v_res_4030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(v_00_u03b2_4022_, v_x_4023_, v_x_31551__boxed_4028_, v_x_31552__boxed_4029_, v_x_4026_, v_x_4027_);
    return v_res_4030_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(
    mut v_map_4031_: *mut crate::leanh::LeanObject,
    mut v_f_4032_: *mut crate::leanh::LeanObject,
    mut v_init_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4032_, v_map_4031_, v_init_4033_);
    return v___x_4034_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(
    mut v_00_u03c3_4035_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4036_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4037_: *mut crate::leanh::LeanObject,
    mut v_map_4038_: *mut crate::leanh::LeanObject,
    mut v_f_4039_: *mut crate::leanh::LeanObject,
    mut v_init_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4039_, v_map_4038_, v_init_4040_);
    return v___x_4041_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(
    mut v_map_4042_: *mut crate::leanh::LeanObject,
    mut v_f_4043_: *mut crate::leanh::LeanObject,
    mut v_init_4044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4043_, v_map_4042_, v_init_4044_);
    return v___x_4045_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(
    mut v_map_4046_: *mut crate::leanh::LeanObject,
    mut v_f_4047_: *mut crate::leanh::LeanObject,
    mut v_init_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(v_map_4046_, v_f_4047_, v_init_4048_);
    crate::leanh::lean_dec_ref(v_map_4046_);
    return v_res_4049_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(
    mut v_00_u03c3_4050_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4051_: *mut crate::leanh::LeanObject,
    mut v_map_4052_: *mut crate::leanh::LeanObject,
    mut v_f_4053_: *mut crate::leanh::LeanObject,
    mut v_init_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4053_, v_map_4052_, v_init_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(
    mut v_00_u03c3_4056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4057_: *mut crate::leanh::LeanObject,
    mut v_map_4058_: *mut crate::leanh::LeanObject,
    mut v_f_4059_: *mut crate::leanh::LeanObject,
    mut v_init_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(v_00_u03c3_4056_, v_00_u03b2_4057_, v_map_4058_, v_f_4059_, v_init_4060_);
    crate::leanh::lean_dec_ref(v_map_4058_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(
    mut v_msgData_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_4062_, v___y_4064_);
    return v___x_4066_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(
    mut v_msgData_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(v_msgData_4067_, v___y_4068_, v___y_4069_);
    crate::leanh::lean_dec(v___y_4069_);
    crate::leanh::lean_dec_ref(v___y_4068_);
    return v_res_4071_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(
    mut v_00_u03b1_4072_: *mut crate::leanh::LeanObject,
    mut v_preNode_4073_: *mut crate::leanh::LeanObject,
    mut v_postNode_4074_: *mut crate::leanh::LeanObject,
    mut v___x_4075_: *mut crate::leanh::LeanObject,
    mut v_x_4076_: *mut crate::leanh::LeanObject,
    mut v_x_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4081_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_4073_, v_postNode_4074_, v___x_4075_, v_x_4076_, v_x_4077_, v___y_4078_, v___y_4079_);
    return v___x_4081_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(
    mut v_00_u03b1_4082_: *mut crate::leanh::LeanObject,
    mut v_preNode_4083_: *mut crate::leanh::LeanObject,
    mut v_postNode_4084_: *mut crate::leanh::LeanObject,
    mut v___x_4085_: *mut crate::leanh::LeanObject,
    mut v_x_4086_: *mut crate::leanh::LeanObject,
    mut v_x_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(v_00_u03b1_4082_, v_preNode_4083_, v_postNode_4084_, v___x_4085_, v_x_4086_, v_x_4087_, v___y_4088_, v___y_4089_);
    crate::leanh::lean_dec(v___y_4089_);
    crate::leanh::lean_dec_ref(v___y_4088_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(
    mut v_00_u03b2_4092_: *mut crate::leanh::LeanObject,
    mut v_keys_4093_: *mut crate::leanh::LeanObject,
    mut v_vals_4094_: *mut crate::leanh::LeanObject,
    mut v_heq_4095_: *mut crate::leanh::LeanObject,
    mut v_i_4096_: *mut crate::leanh::LeanObject,
    mut v_k_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_4093_, v_vals_4094_, v_i_4096_, v_k_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(
    mut v_00_u03b2_4099_: *mut crate::leanh::LeanObject,
    mut v_keys_4100_: *mut crate::leanh::LeanObject,
    mut v_vals_4101_: *mut crate::leanh::LeanObject,
    mut v_heq_4102_: *mut crate::leanh::LeanObject,
    mut v_i_4103_: *mut crate::leanh::LeanObject,
    mut v_k_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4105_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(v_00_u03b2_4099_, v_keys_4100_, v_vals_4101_, v_heq_4102_, v_i_4103_, v_k_4104_);
    crate::leanh::lean_dec(v_k_4104_);
    crate::leanh::lean_dec_ref(v_vals_4101_);
    crate::leanh::lean_dec_ref(v_keys_4100_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(
    mut v_00_u03b2_4106_: *mut crate::leanh::LeanObject,
    mut v_n_4107_: *mut crate::leanh::LeanObject,
    mut v_k_4108_: *mut crate::leanh::LeanObject,
    mut v_v_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v_n_4107_, v_k_4108_, v_v_4109_);
    return v___x_4110_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(
    mut v_00_u03b2_4111_: *mut crate::leanh::LeanObject,
    mut v_depth_4112_: usize,
    mut v_keys_4113_: *mut crate::leanh::LeanObject,
    mut v_vals_4114_: *mut crate::leanh::LeanObject,
    mut v_heq_4115_: *mut crate::leanh::LeanObject,
    mut v_i_4116_: *mut crate::leanh::LeanObject,
    mut v_entries_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_4112_, v_keys_4113_, v_vals_4114_, v_i_4116_, v_entries_4117_);
    return v___x_4118_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(
    mut v_00_u03b2_4119_: *mut crate::leanh::LeanObject,
    mut v_depth_4120_: *mut crate::leanh::LeanObject,
    mut v_keys_4121_: *mut crate::leanh::LeanObject,
    mut v_vals_4122_: *mut crate::leanh::LeanObject,
    mut v_heq_4123_: *mut crate::leanh::LeanObject,
    mut v_i_4124_: *mut crate::leanh::LeanObject,
    mut v_entries_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4126_: usize = 0;
    let mut v_res_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4126_ = crate::leanh::lean_unbox_usize(v_depth_4120_);
    crate::leanh::lean_dec(v_depth_4120_);
    v_res_4127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(v_00_u03b2_4119_, v_depth_boxed_4126_, v_keys_4121_, v_vals_4122_, v_heq_4123_, v_i_4124_, v_entries_4125_);
    crate::leanh::lean_dec_ref(v_vals_4122_);
    crate::leanh::lean_dec_ref(v_keys_4121_);
    return v_res_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(
    mut v_00_u03c3_4128_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4131_: *mut crate::leanh::LeanObject,
    mut v_f_4132_: *mut crate::leanh::LeanObject,
    mut v_x_4133_: *mut crate::leanh::LeanObject,
    mut v_x_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4132_, v_x_4133_, v_x_4134_);
    return v___x_4135_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(
    mut v_00_u03c3_4136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4138_: *mut crate::leanh::LeanObject,
    mut v_f_4139_: *mut crate::leanh::LeanObject,
    mut v_x_4140_: *mut crate::leanh::LeanObject,
    mut v_x_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4139_, v_x_4140_, v_x_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(
    mut v_00_u03c3_4143_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4145_: *mut crate::leanh::LeanObject,
    mut v_f_4146_: *mut crate::leanh::LeanObject,
    mut v_x_4147_: *mut crate::leanh::LeanObject,
    mut v_x_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(v_00_u03c3_4143_, v_00_u03b1_4144_, v_00_u03b2_4145_, v_f_4146_, v_x_4147_, v_x_4148_);
    crate::leanh::lean_dec_ref(v_x_4147_);
    return v_res_4149_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(
    mut v_00_u03b2_4150_: *mut crate::leanh::LeanObject,
    mut v_x_4151_: *mut crate::leanh::LeanObject,
    mut v_x_4152_: *mut crate::leanh::LeanObject,
    mut v_x_4153_: *mut crate::leanh::LeanObject,
    mut v_x_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4155_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_x_4151_, v_x_4152_, v_x_4153_, v_x_4154_);
    return v___x_4155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(
    mut v_00_u03b1_4156_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4157_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4158_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4159_: *mut crate::leanh::LeanObject,
    mut v_f_4160_: *mut crate::leanh::LeanObject,
    mut v_as_4161_: *mut crate::leanh::LeanObject,
    mut v_i_4162_: usize,
    mut v_stop_4163_: usize,
    mut v_b_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_4160_, v_as_4161_, v_i_4162_, v_stop_4163_, v_b_4164_);
    return v___x_4165_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(
    mut v_00_u03b1_4166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4167_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4168_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4169_: *mut crate::leanh::LeanObject,
    mut v_f_4170_: *mut crate::leanh::LeanObject,
    mut v_as_4171_: *mut crate::leanh::LeanObject,
    mut v_i_4172_: *mut crate::leanh::LeanObject,
    mut v_stop_4173_: *mut crate::leanh::LeanObject,
    mut v_b_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4175_: usize = 0;
    let mut v_stop_boxed_4176_: usize = 0;
    let mut v_res_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4175_ = crate::leanh::lean_unbox_usize(v_i_4172_);
    crate::leanh::lean_dec(v_i_4172_);
    v_stop_boxed_4176_ = crate::leanh::lean_unbox_usize(v_stop_4173_);
    crate::leanh::lean_dec(v_stop_4173_);
    v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(v_00_u03b1_4166_, v_00_u03b2_4167_, v_00_u03c3_4168_, v_00_u03c3_4169_, v_f_4170_, v_as_4171_, v_i_boxed_4175_, v_stop_boxed_4176_, v_b_4174_);
    crate::leanh::lean_dec_ref(v_as_4171_);
    return v_res_4177_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(
    mut v_00_u03c3_4178_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4179_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4180_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4181_: *mut crate::leanh::LeanObject,
    mut v_f_4182_: *mut crate::leanh::LeanObject,
    mut v_keys_4183_: *mut crate::leanh::LeanObject,
    mut v_vals_4184_: *mut crate::leanh::LeanObject,
    mut v_heq_4185_: *mut crate::leanh::LeanObject,
    mut v_i_4186_: *mut crate::leanh::LeanObject,
    mut v_acc_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_4182_, v_keys_4183_, v_vals_4184_, v_i_4186_, v_acc_4187_);
    return v___x_4188_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(
    mut v_00_u03c3_4189_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4190_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4191_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4192_: *mut crate::leanh::LeanObject,
    mut v_f_4193_: *mut crate::leanh::LeanObject,
    mut v_keys_4194_: *mut crate::leanh::LeanObject,
    mut v_vals_4195_: *mut crate::leanh::LeanObject,
    mut v_heq_4196_: *mut crate::leanh::LeanObject,
    mut v_i_4197_: *mut crate::leanh::LeanObject,
    mut v_acc_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(v_00_u03c3_4189_, v_00_u03c3_4190_, v_00_u03b1_4191_, v_00_u03b2_4192_, v_f_4193_, v_keys_4194_, v_vals_4195_, v_heq_4196_, v_i_4197_, v_acc_4198_);
    crate::leanh::lean_dec_ref(v_vals_4195_);
    crate::leanh::lean_dec_ref(v_keys_4194_);
    return v_res_4199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(
    mut v_00_u03b1_4200_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4201_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4202_: *mut crate::leanh::LeanObject,
    mut v_f_4203_: *mut crate::leanh::LeanObject,
    mut v_as_4204_: *mut crate::leanh::LeanObject,
    mut v_i_4205_: usize,
    mut v_stop_4206_: usize,
    mut v_b_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_4203_, v_as_4204_, v_i_4205_, v_stop_4206_, v_b_4207_);
    return v___x_4208_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(
    mut v_00_u03b1_4209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4210_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4211_: *mut crate::leanh::LeanObject,
    mut v_f_4212_: *mut crate::leanh::LeanObject,
    mut v_as_4213_: *mut crate::leanh::LeanObject,
    mut v_i_4214_: *mut crate::leanh::LeanObject,
    mut v_stop_4215_: *mut crate::leanh::LeanObject,
    mut v_b_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4217_: usize = 0;
    let mut v_stop_boxed_4218_: usize = 0;
    let mut v_res_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4217_ = crate::leanh::lean_unbox_usize(v_i_4214_);
    crate::leanh::lean_dec(v_i_4214_);
    v_stop_boxed_4218_ = crate::leanh::lean_unbox_usize(v_stop_4215_);
    crate::leanh::lean_dec(v_stop_4215_);
    v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(v_00_u03b1_4209_, v_00_u03b2_4210_, v_00_u03c3_4211_, v_f_4212_, v_as_4213_, v_i_boxed_4217_, v_stop_boxed_4218_, v_b_4216_);
    crate::leanh::lean_dec_ref(v_as_4213_);
    return v_res_4219_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(
    mut v_00_u03c3_4220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4222_: *mut crate::leanh::LeanObject,
    mut v_f_4223_: *mut crate::leanh::LeanObject,
    mut v_keys_4224_: *mut crate::leanh::LeanObject,
    mut v_vals_4225_: *mut crate::leanh::LeanObject,
    mut v_heq_4226_: *mut crate::leanh::LeanObject,
    mut v_i_4227_: *mut crate::leanh::LeanObject,
    mut v_acc_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_4223_, v_keys_4224_, v_vals_4225_, v_i_4227_, v_acc_4228_);
    return v___x_4229_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(
    mut v_00_u03c3_4230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4232_: *mut crate::leanh::LeanObject,
    mut v_f_4233_: *mut crate::leanh::LeanObject,
    mut v_keys_4234_: *mut crate::leanh::LeanObject,
    mut v_vals_4235_: *mut crate::leanh::LeanObject,
    mut v_heq_4236_: *mut crate::leanh::LeanObject,
    mut v_i_4237_: *mut crate::leanh::LeanObject,
    mut v_acc_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(v_00_u03c3_4230_, v_00_u03b1_4231_, v_00_u03b2_4232_, v_f_4233_, v_keys_4234_, v_vals_4235_, v_heq_4236_, v_i_4237_, v_acc_4238_);
    crate::leanh::lean_dec_ref(v_vals_4235_);
    crate::leanh::lean_dec_ref(v_keys_4234_);
    return v_res_4239_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances;
    v___x_4242_ = l_Lean_Elab_Command_addLinter(v___x_4241_);
    return v___x_4242_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(
    mut v_a_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
    return v_res_4244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_TacticTypeCheck(
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
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_TacticTypeCheck(
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
pub unsafe fn initialize_Lean_Linter_TacticTypeCheck(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_TacticTypeCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_TacticTypeCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_TacticTypeCheck(builtin);
}
