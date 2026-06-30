// Lean compiler output
// Module: Lean.Linter.TacticTypeCheck
// Imports: Lean.Elab.Command Lean.Linter.Util Lean.Meta.Check Lean.Meta.Diagnostics
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [116, 97, 99, 116, 105, 99, 67, 104, 101, 99, 107, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,3877803915353198398 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<82> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 108, 105, 110, 116, 101, 114, 32, 116, 104, 97, 116, 32, 116, 121, 112, 101, 45, 99, 104, 101, 99, 107, 115, 32, 101, 118, 101, 114, 121, 32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4424989899264441540 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [84, 97, 99, 116, 105, 99, 84, 121, 112, 101, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10581205489494877745 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1816322908595936884 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,1896795829154494325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8582532011273483831 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,3028325180435466294 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,3528273497824055570 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value: leanh::LeanStringObject<62> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 105, 116, 105, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 100, 117, 99, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value: leanh::LeanStringObject<64> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101, 45, 99, 111, 114, 114, 101, 99, 116, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 59, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [32, 115, 111, 109, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 97, 115, 32, 96, 64, 91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 58, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [10, 70, 117, 108, 108, 32, 101, 114, 114, 111, 114, 58, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 111, 114, 32, 109, 97, 114, 107, 105, 110, 103, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 111, 110, 115, 105, 100, 101, 114, 32, 114, 101, 112, 104, 114, 97, 115, 105, 110, 103, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 111, 114, 32, 109, 97, 114, 107, 105, 110, 103, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value) as *mut leanh::LeanObject,16625058045004708007 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(
    mut v_name_2123_: *mut leanh::LeanObject,
    mut v_decl_2124_: *mut leanh::LeanObject,
    mut v_ref_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_unused_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2127_ = leanh::lean_ctor_get(v_decl_2124_, 0);
                v_descr_2128_ = leanh::lean_ctor_get(v_decl_2124_, 1);
                v_deprecation_x3f_2129_ = leanh::lean_ctor_get(v_decl_2124_, 2);
                v___x_2130_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2131_ = (leanh::lean_unbox(v_defValue_2127_) as u8);
                leanh::lean_ctor_set_uint8(v___x_2130_, 0 as u32, v___x_2131_);
                leanh::lean_inc(v_deprecation_x3f_2129_);
                leanh::lean_inc_ref(v_descr_2128_);
                leanh::lean_inc_n(v_name_2123_, 2);
                v___x_2132_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2132_, 0, v_name_2123_);
                leanh::lean_ctor_set(v___x_2132_, 1, v_ref_2125_);
                leanh::lean_ctor_set(v___x_2132_, 2, v___x_2130_);
                leanh::lean_ctor_set(v___x_2132_, 3, v_descr_2128_);
                leanh::lean_ctor_set(v___x_2132_, 4, v_deprecation_x3f_2129_);
                v___x_2133_ = lean_register_option(v_name_2123_, v___x_2132_);
                if leanh::lean_obj_tag(v___x_2133_) == 0 {
                    v_isSharedCheck_2141_ = (!leanh::lean_is_exclusive(v___x_2133_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v_unused_2142_ = leanh::lean_ctor_get(v___x_2133_, 0);
                        leanh::lean_dec(v_unused_2142_);
                        v___x_2135_ = v___x_2133_;
                        v_isShared_2136_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2133_);
                        v___x_2135_ = leanh::lean_box(0);
                        v_isShared_2136_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2123_);
                    v_a_2143_ = leanh::lean_ctor_get(v___x_2133_, 0);
                    v_isSharedCheck_2150_ = (!leanh::lean_is_exclusive(v___x_2133_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2133_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2143_);
                        leanh::lean_dec(v___x_2133_);
                        v___x_2145_ = leanh::lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_2127_);
                v___x_2137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2137_, 0, v_name_2123_);
                leanh::lean_ctor_set(v___x_2137_, 1, v_defValue_2127_);
                if v_isShared_2136_ == 0 {
                    leanh::lean_ctor_set(v___x_2135_, 0, v___x_2137_);
                    v___x_2139_ = v___x_2135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
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
                    v_reuseFailAlloc_2149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
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
    mut v_name_2151_: *mut leanh::LeanObject,
    mut v_decl_2152_: *mut leanh::LeanObject,
    mut v_ref_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v_name_2151_, v_decl_2152_, v_ref_2153_);
    leanh::lean_dec_ref(v_decl_2152_);
    return v_res_2155_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2200_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2201_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_;
    v___x_2202_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v___x_2199_, v___x_2200_, v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4____boxed(
    mut v_a_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
    return v_res_2204_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(
    mut v_e_2205_: *mut leanh::LeanObject,
    mut v___y_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2208_ = l_Lean_Expr_hasMVar(v_e_2205_);
                if v___x_2208_ == 0 {
                    v___x_2209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2209_, 0, v_e_2205_);
                    return v___x_2209_;
                } else {
                    v___x_2210_ = lean_st_ref_get(v___y_2206_);
                    v_mctx_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                    leanh::lean_inc_ref(v_mctx_2211_);
                    leanh::lean_dec(v___x_2210_);
                    v___x_2212_ = l_Lean_instantiateMVarsCore(v_mctx_2211_, v_e_2205_);
                    v_fst_2213_ = leanh::lean_ctor_get(v___x_2212_, 0);
                    leanh::lean_inc(v_fst_2213_);
                    v_snd_2214_ = leanh::lean_ctor_get(v___x_2212_, 1);
                    leanh::lean_inc(v_snd_2214_);
                    leanh::lean_dec_ref(v___x_2212_);
                    v___x_2215_ = lean_st_ref_take(v___y_2206_);
                    v_cache_2216_ = leanh::lean_ctor_get(v___x_2215_, 1);
                    v_zetaDeltaFVarIds_2217_ = leanh::lean_ctor_get(v___x_2215_, 2);
                    v_postponed_2218_ = leanh::lean_ctor_get(v___x_2215_, 3);
                    v_diag_2219_ = leanh::lean_ctor_get(v___x_2215_, 4);
                    v_isSharedCheck_2228_ = (!leanh::lean_is_exclusive(v___x_2215_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v_unused_2229_ = leanh::lean_ctor_get(v___x_2215_, 0);
                        leanh::lean_dec(v_unused_2229_);
                        v___x_2221_ = v___x_2215_;
                        v_isShared_2222_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2219_);
                        leanh::lean_inc(v_postponed_2218_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2217_);
                        leanh::lean_inc(v_cache_2216_);
                        leanh::lean_dec(v___x_2215_);
                        v___x_2221_ = leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2222_ == 0 {
                    leanh::lean_ctor_set(v___x_2221_, 0, v_snd_2214_);
                    v___x_2224_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_snd_2214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_cache_2216_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2227_,
                        2,
                        v_zetaDeltaFVarIds_2217_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_postponed_2218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_diag_2219_);
                    v___x_2224_ = v_reuseFailAlloc_2227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2225_ = lean_st_ref_set(v___y_2206_, v___x_2224_);
                v___x_2226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2226_, 0, v_fst_2213_);
                return v___x_2226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg___boxed(
    mut v_e_2230_: *mut leanh::LeanObject,
    mut v___y_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_2230_, v___y_2231_);
    leanh::lean_dec(v___y_2231_);
    return v_res_2233_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(
    mut v_e_2234_: *mut leanh::LeanObject,
    mut v___y_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_2234_, v___y_2236_);
    return v___x_2240_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___boxed(
    mut v_e_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(v_e_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
    leanh::lean_dec(v___y_2245_);
    leanh::lean_dec_ref(v___y_2244_);
    leanh::lean_dec(v___y_2243_);
    leanh::lean_dec_ref(v___y_2242_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(
    mut v_opts_2248_: *mut leanh::LeanObject,
    mut v_opt_2249_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2250_ = leanh::lean_ctor_get(v_opt_2249_, 0);
    v_defValue_2251_ = leanh::lean_ctor_get(v_opt_2249_, 1);
    v_map_2252_ = leanh::lean_ctor_get(v_opts_2248_, 0);
    v___x_2253_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2252_,
            v_name_2250_,
        );
    if leanh::lean_obj_tag(v___x_2253_) == 0 {
        let mut v___x_2254_: u8 = 0;
        v___x_2254_ = (leanh::lean_unbox(v_defValue_2251_) as u8);
        return v___x_2254_;
    } else {
        let mut v_val_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2255_ = leanh::lean_ctor_get(v___x_2253_, 0);
        leanh::lean_inc(v_val_2255_);
        leanh::lean_dec_ref_known(v___x_2253_, 1);
        if leanh::lean_obj_tag(v_val_2255_) == 1 {
            let mut v_v_2256_: u8 = 0;
            v_v_2256_ = leanh::lean_ctor_get_uint8(v_val_2255_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2255_, 0);
            return v_v_2256_;
        } else {
            let mut v___x_2257_: u8 = 0;
            leanh::lean_dec(v_val_2255_);
            v___x_2257_ = (leanh::lean_unbox(v_defValue_2251_) as u8);
            return v___x_2257_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(
    mut v_opts_2258_: *mut leanh::LeanObject,
    mut v_opt_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2260_: u8 = 0;
    let mut v_r_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2258_, v_opt_2259_);
    leanh::lean_dec_ref(v_opt_2259_);
    leanh::lean_dec_ref(v_opts_2258_);
    v_r_2261_ = leanh::lean_box((v_res_2260_) as usize);
    return v_r_2261_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(
    mut v_opts_2262_: *mut leanh::LeanObject,
    mut v_opt_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2264_ = leanh::lean_ctor_get(v_opt_2263_, 0);
    v_defValue_2265_ = leanh::lean_ctor_get(v_opt_2263_, 1);
    v_map_2266_ = leanh::lean_ctor_get(v_opts_2262_, 0);
    v___x_2267_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2266_,
            v_name_2264_,
        );
    if leanh::lean_obj_tag(v___x_2267_) == 0 {
        leanh::lean_inc(v_defValue_2265_);
        return v_defValue_2265_;
    } else {
        let mut v_val_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2268_ = leanh::lean_ctor_get(v___x_2267_, 0);
        leanh::lean_inc(v_val_2268_);
        leanh::lean_dec_ref_known(v___x_2267_, 1);
        if leanh::lean_obj_tag(v_val_2268_) == 3 {
            let mut v_v_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2269_ = leanh::lean_ctor_get(v_val_2268_, 0);
            leanh::lean_inc(v_v_2269_);
            leanh::lean_dec_ref_known(v_val_2268_, 1);
            return v_v_2269_;
        } else {
            leanh::lean_dec(v_val_2268_);
            leanh::lean_inc(v_defValue_2265_);
            return v_defValue_2265_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(
    mut v_opts_2270_: *mut leanh::LeanObject,
    mut v_opt_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_opts_2270_, v_opt_2271_);
    leanh::lean_dec_ref(v_opt_2271_);
    leanh::lean_dec_ref(v_opts_2270_);
    return v_res_2272_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(
    mut v_lctx_2273_: *mut leanh::LeanObject,
    mut v_localInsts_2274_: *mut leanh::LeanObject,
    mut v_x_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    leanh::lean_box(0),
                    v_lctx_2273_,
                    v_localInsts_2274_,
                    v_x_2275_,
                    v___y_2276_,
                    v___y_2277_,
                    v___y_2278_,
                    v___y_2279_,
                );
                if leanh::lean_obj_tag(v___x_2281_) == 0 {
                    v_a_2282_ = leanh::lean_ctor_get(v___x_2281_, 0);
                    v_isSharedCheck_2289_ = (!leanh::lean_is_exclusive(v___x_2281_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2284_ = v___x_2281_;
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2282_);
                        leanh::lean_dec(v___x_2281_);
                        v___x_2284_ = leanh::lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2290_ = leanh::lean_ctor_get(v___x_2281_, 0);
                    v_isSharedCheck_2297_ = (!leanh::lean_is_exclusive(v___x_2281_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v___x_2292_ = v___x_2281_;
                        v_isShared_2293_ = v_isSharedCheck_2297_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2290_);
                        leanh::lean_dec(v___x_2281_);
                        v___x_2292_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
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
                    v_reuseFailAlloc_2296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
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
    mut v_lctx_2298_: *mut leanh::LeanObject,
    mut v_localInsts_2299_: *mut leanh::LeanObject,
    mut v_x_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2306_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_2298_, v_localInsts_2299_, v_x_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
    leanh::lean_dec(v___y_2304_);
    leanh::lean_dec_ref(v___y_2303_);
    leanh::lean_dec(v___y_2302_);
    leanh::lean_dec_ref(v___y_2301_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(
    mut v_00_u03b1_2307_: *mut leanh::LeanObject,
    mut v_lctx_2308_: *mut leanh::LeanObject,
    mut v_localInsts_2309_: *mut leanh::LeanObject,
    mut v_x_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_2308_, v_localInsts_2309_, v_x_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
    return v___x_2316_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(
    mut v_00_u03b1_2317_: *mut leanh::LeanObject,
    mut v_lctx_2318_: *mut leanh::LeanObject,
    mut v_localInsts_2319_: *mut leanh::LeanObject,
    mut v_x_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_00_u03b1_2317_, v_lctx_2318_, v_localInsts_2319_, v_x_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
    leanh::lean_dec(v___y_2324_);
    leanh::lean_dec_ref(v___y_2323_);
    leanh::lean_dec(v___y_2322_);
    leanh::lean_dec_ref(v___y_2321_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(
    mut v_opt_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = lean_st_ref_get(v___y_2328_);
    v_scopes_2331_ = leanh::lean_ctor_get(v___x_2330_, 2);
    leanh::lean_inc(v_scopes_2331_);
    leanh::lean_dec(v___x_2330_);
    v___x_2332_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2333_ = l_List_head_x21___redArg(v___x_2332_, v_scopes_2331_);
    leanh::lean_dec(v_scopes_2331_);
    v_opts_2334_ = leanh::lean_ctor_get(v___x_2333_, 1);
    leanh::lean_inc_ref(v_opts_2334_);
    leanh::lean_dec(v___x_2333_);
    v___x_2335_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2334_, v_opt_2327_);
    leanh::lean_dec_ref(v_opts_2334_);
    v___x_2336_ = leanh::lean_box((v___x_2335_) as usize);
    v___x_2337_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(
    mut v_opt_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_2338_, v___y_2339_);
    leanh::lean_dec(v___y_2339_);
    leanh::lean_dec_ref(v_opt_2338_);
    return v_res_2341_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(
    mut v_a_2342_: u8,
    mut v_x_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_x_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = leanh::lean_box((v_a_2342_) as usize);
    v___x_2350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed(
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_x_2352_: *mut leanh::LeanObject,
    mut v_x_2353_: *mut leanh::LeanObject,
    mut v_x_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_28976__boxed_2358_: u8 = 0;
    let mut v_res_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_28976__boxed_2358_ = (leanh::lean_unbox(v_a_2351_) as u8);
    v_res_2359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(v_a_28976__boxed_2358_, v_x_2352_, v_x_2353_, v_x_2354_, v___y_2355_, v___y_2356_);
    leanh::lean_dec(v___y_2356_);
    leanh::lean_dec_ref(v___y_2355_);
    leanh::lean_dec_ref(v_x_2354_);
    leanh::lean_dec_ref(v_x_2353_);
    leanh::lean_dec_ref(v_x_2352_);
    return v_res_2359_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(
    mut v_postNode_2360_: *mut leanh::LeanObject,
    mut v_ci_2361_: *mut leanh::LeanObject,
    mut v_i_2362_: *mut leanh::LeanObject,
    mut v_cs_2363_: *mut leanh::LeanObject,
    mut v_x_2364_: *mut leanh::LeanObject,
    mut v___y_2365_: *mut leanh::LeanObject,
    mut v___y_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2366_);
    leanh::lean_inc_ref(v___y_2365_);
    v___x_2368_ = leanh::lean_apply_6(
        v_postNode_2360_,
        v_ci_2361_,
        v_i_2362_,
        v_cs_2363_,
        v___y_2365_,
        v___y_2366_,
        leanh::lean_box(0),
    );
    return v___x_2368_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(
    mut v_postNode_2369_: *mut leanh::LeanObject,
    mut v_ci_2370_: *mut leanh::LeanObject,
    mut v_i_2371_: *mut leanh::LeanObject,
    mut v_cs_2372_: *mut leanh::LeanObject,
    mut v_x_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
    mut v___y_2375_: *mut leanh::LeanObject,
    mut v___y_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_postNode_2369_, v_ci_2370_, v_i_2371_, v_cs_2372_, v_x_2373_, v___y_2374_, v___y_2375_);
    leanh::lean_dec(v___y_2375_);
    leanh::lean_dec_ref(v___y_2374_);
    leanh::lean_dec(v_x_2373_);
    return v_res_2377_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2378_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(
    mut v_msg_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: *mut leanh::LeanObject,
    mut v___y_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_toFunctor_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___f_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_25987__overap_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v_unused_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2385_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once), _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0);
                v___x_2386_ = l_StateRefT_x27_instMonad___redArg(v___x_2385_);
                v_toApplicative_2387_ = leanh::lean_ctor_get(v___x_2386_, 0);
                v_isSharedCheck_2418_ = (!leanh::lean_is_exclusive(v___x_2386_)) as u8;
                if v_isSharedCheck_2418_ == 0 {
                    v_unused_2419_ = leanh::lean_ctor_get(v___x_2386_, 1);
                    leanh::lean_dec(v_unused_2419_);
                    v___x_2389_ = v___x_2386_;
                    v_isShared_2390_ = v_isSharedCheck_2418_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2387_);
                    leanh::lean_dec(v___x_2386_);
                    v___x_2389_ = leanh::lean_box(0);
                    v_isShared_2390_ = v_isSharedCheck_2418_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2391_ = leanh::lean_ctor_get(v_toApplicative_2387_, 0);
                v_toSeq_2392_ = leanh::lean_ctor_get(v_toApplicative_2387_, 2);
                v_toSeqLeft_2393_ = leanh::lean_ctor_get(v_toApplicative_2387_, 3);
                v_toSeqRight_2394_ = leanh::lean_ctor_get(v_toApplicative_2387_, 4);
                v_isSharedCheck_2416_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2387_)) as u8;
                if v_isSharedCheck_2416_ == 0 {
                    v_unused_2417_ = leanh::lean_ctor_get(v_toApplicative_2387_, 1);
                    leanh::lean_dec(v_unused_2417_);
                    v___x_2396_ = v_toApplicative_2387_;
                    v_isShared_2397_ = v_isSharedCheck_2416_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2394_);
                    leanh::lean_inc(v_toSeqLeft_2393_);
                    leanh::lean_inc(v_toSeq_2392_);
                    leanh::lean_inc(v_toFunctor_2391_);
                    leanh::lean_dec(v_toApplicative_2387_);
                    v___x_2396_ = leanh::lean_box(0);
                    v_isShared_2397_ = v_isSharedCheck_2416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2398_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1;
                v___f_2399_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2;
                leanh::lean_inc_ref(v_toFunctor_2391_);
                v___f_2400_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2400_, 0, v_toFunctor_2391_);
                v___f_2401_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2401_, 0, v_toFunctor_2391_);
                v___x_2402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2402_, 0, v___f_2400_);
                leanh::lean_ctor_set(v___x_2402_, 1, v___f_2401_);
                v___f_2403_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2403_, 0, v_toSeqRight_2394_);
                v___f_2404_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2404_, 0, v_toSeqLeft_2393_);
                v___f_2405_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2405_, 0, v_toSeq_2392_);
                if v_isShared_2397_ == 0 {
                    leanh::lean_ctor_set(v___x_2396_, 4, v___f_2403_);
                    leanh::lean_ctor_set(v___x_2396_, 3, v___f_2404_);
                    leanh::lean_ctor_set(v___x_2396_, 2, v___f_2405_);
                    leanh::lean_ctor_set(v___x_2396_, 1, v___f_2398_);
                    leanh::lean_ctor_set(v___x_2396_, 0, v___x_2402_);
                    v___x_2407_ = v___x_2396_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2415_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___f_2398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___f_2405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 3, v___f_2404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 4, v___f_2403_);
                    v___x_2407_ = v_reuseFailAlloc_2415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2390_ == 0 {
                    leanh::lean_ctor_set(v___x_2389_, 1, v___f_2399_);
                    leanh::lean_ctor_set(v___x_2389_, 0, v___x_2407_);
                    v___x_2409_ = v___x_2389_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___f_2399_);
                    v___x_2409_ = v_reuseFailAlloc_2414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2410_ = leanh::lean_box(0);
                v___x_2411_ = l_instInhabitedOfMonad___redArg(v___x_2409_, v___x_2410_);
                v___x_25987__overap_2412_ = lean_panic_fn_borrowed(v___x_2411_, v_msg_2381_);
                leanh::lean_dec(v___x_2411_);
                leanh::lean_inc(v___y_2383_);
                leanh::lean_inc_ref(v___y_2382_);
                v___x_2413_ = leanh::lean_apply_3(
                    v___x_25987__overap_2412_,
                    v___y_2382_,
                    v___y_2383_,
                    leanh::lean_box(0),
                );
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___boxed(
    mut v_msg_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_2420_, v___y_2421_, v___y_2422_);
    leanh::lean_dec(v___y_2422_);
    leanh::lean_dec_ref(v___y_2421_);
    return v_res_2424_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2428_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2;
    v___x_2429_ = leanh::lean_unsigned_to_nat(21);
    v___x_2430_ = leanh::lean_unsigned_to_nat(65);
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
    mut v_preNode_2434_: *mut leanh::LeanObject,
    mut v_postNode_2435_: *mut leanh::LeanObject,
    mut v_x_2436_: *mut leanh::LeanObject,
    mut v_x_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_a_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2472_: u8 = 0;
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v_unused_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_a_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v_a_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2517_: u8 = 0;
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_unused_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2437_) {
                0 => {
                    v_i_2441_ = leanh::lean_ctor_get(v_x_2437_, 0);
                    leanh::lean_inc_ref(v_i_2441_);
                    v_t_2442_ = leanh::lean_ctor_get(v_x_2437_, 1);
                    leanh::lean_inc_ref(v_t_2442_);
                    leanh::lean_dec_ref_known(v_x_2437_, 2);
                    v___x_2443_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2441_, v_x_2436_);
                    v_x_2436_ = v___x_2443_;
                    v_x_2437_ = v_t_2442_;
                    state = 0;
                    continue;
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_2436_) == 0 {
                        leanh::lean_dec_ref_known(v_x_2437_, 2);
                        leanh::lean_dec_ref(v_postNode_2435_);
                        leanh::lean_dec_ref(v_preNode_2434_);
                        v___x_2445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3);
                        v___x_2446_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v___x_2445_, v___y_2438_, v___y_2439_);
                        return v___x_2446_;
                    } else {
                        v_i_2447_ = leanh::lean_ctor_get(v_x_2437_, 0);
                        leanh::lean_inc_ref_n(v_i_2447_, 2);
                        v_children_2448_ = leanh::lean_ctor_get(v_x_2437_, 1);
                        leanh::lean_inc_ref_n(v_children_2448_, 2);
                        leanh::lean_dec_ref_known(v_x_2437_, 2);
                        v_val_2449_ = leanh::lean_ctor_get(v_x_2436_, 0);
                        leanh::lean_inc_n(v_val_2449_, 2);
                        leanh::lean_inc_ref(v_preNode_2434_);
                        leanh::lean_inc(v___y_2439_);
                        leanh::lean_inc_ref(v___y_2438_);
                        v___x_2450_ = leanh::lean_apply_6(
                            v_preNode_2434_,
                            v_val_2449_,
                            v_i_2447_,
                            v_children_2448_,
                            v___y_2438_,
                            v___y_2439_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_2450_) == 0 {
                            v_a_2451_ = leanh::lean_ctor_get(v___x_2450_, 0);
                            leanh::lean_inc(v_a_2451_);
                            leanh::lean_dec_ref_known(v___x_2450_, 1);
                            v___x_2452_ = (leanh::lean_unbox(v_a_2451_) as u8);
                            leanh::lean_dec(v_a_2451_);
                            if v___x_2452_ == 0 {
                                leanh::lean_dec_ref(v_preNode_2434_);
                                v_isSharedCheck_2477_ =
                                    (!leanh::lean_is_exclusive(v_x_2436_)) as u8;
                                if v_isSharedCheck_2477_ == 0 {
                                    v_unused_2478_ = leanh::lean_ctor_get(v_x_2436_, 0);
                                    leanh::lean_dec(v_unused_2478_);
                                    v___x_2454_ = v_x_2436_;
                                    v_isShared_2455_ = v_isSharedCheck_2477_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_2436_);
                                    v___x_2454_ = leanh::lean_box(0);
                                    v_isShared_2455_ = v_isSharedCheck_2477_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2479_ =
                                    l_Lean_Elab_Info_updateContext_x3f(v_x_2436_, v_i_2447_);
                                v___x_2480_ =
                                    l_Lean_PersistentArray_toList___redArg(v_children_2448_);
                                v___x_2481_ = leanh::lean_box(0);
                                leanh::lean_inc_ref(v_postNode_2435_);
                                v___x_2482_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_2434_, v_postNode_2435_, v___x_2479_, v___x_2480_, v___x_2481_, v___y_2438_, v___y_2439_);
                                if leanh::lean_obj_tag(v___x_2482_) == 0 {
                                    v_a_2483_ = leanh::lean_ctor_get(v___x_2482_, 0);
                                    leanh::lean_inc(v_a_2483_);
                                    leanh::lean_dec_ref_known(v___x_2482_, 1);
                                    leanh::lean_inc(v___y_2439_);
                                    leanh::lean_inc_ref(v___y_2438_);
                                    v___x_2484_ = leanh::lean_apply_7(
                                        v_postNode_2435_,
                                        v_val_2449_,
                                        v_i_2447_,
                                        v_children_2448_,
                                        v_a_2483_,
                                        v___y_2438_,
                                        v___y_2439_,
                                        leanh::lean_box(0),
                                    );
                                    if leanh::lean_obj_tag(v___x_2484_) == 0 {
                                        v_a_2485_ = leanh::lean_ctor_get(v___x_2484_, 0);
                                        v_isSharedCheck_2493_ =
                                            (!leanh::lean_is_exclusive(v___x_2484_)) as u8;
                                        if v_isSharedCheck_2493_ == 0 {
                                            v___x_2487_ = v___x_2484_;
                                            v_isShared_2488_ = v_isSharedCheck_2493_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2485_);
                                            leanh::lean_dec(v___x_2484_);
                                            v___x_2487_ = leanh::lean_box(0);
                                            v_isShared_2488_ = v_isSharedCheck_2493_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_2494_ = leanh::lean_ctor_get(v___x_2484_, 0);
                                        v_isSharedCheck_2501_ =
                                            (!leanh::lean_is_exclusive(v___x_2484_)) as u8;
                                        if v_isSharedCheck_2501_ == 0 {
                                            v___x_2496_ = v___x_2484_;
                                            v_isShared_2497_ = v_isSharedCheck_2501_;
                                            state = 9;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2494_);
                                            leanh::lean_dec(v___x_2484_);
                                            v___x_2496_ = leanh::lean_box(0);
                                            v_isShared_2497_ = v_isSharedCheck_2501_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_val_2449_);
                                    leanh::lean_dec_ref(v_children_2448_);
                                    leanh::lean_dec_ref(v_i_2447_);
                                    leanh::lean_dec_ref(v_postNode_2435_);
                                    v_a_2502_ = leanh::lean_ctor_get(v___x_2482_, 0);
                                    v_isSharedCheck_2509_ =
                                        (!leanh::lean_is_exclusive(v___x_2482_)) as u8;
                                    if v_isSharedCheck_2509_ == 0 {
                                        v___x_2504_ = v___x_2482_;
                                        v_isShared_2505_ = v_isSharedCheck_2509_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2502_);
                                        leanh::lean_dec(v___x_2482_);
                                        v___x_2504_ = leanh::lean_box(0);
                                        v_isShared_2505_ = v_isSharedCheck_2509_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_2449_);
                            leanh::lean_dec_ref(v_children_2448_);
                            leanh::lean_dec_ref(v_i_2447_);
                            leanh::lean_dec_ref_known(v_x_2436_, 1);
                            leanh::lean_dec_ref(v_postNode_2435_);
                            leanh::lean_dec_ref(v_preNode_2434_);
                            v_a_2510_ = leanh::lean_ctor_get(v___x_2450_, 0);
                            v_isSharedCheck_2517_ =
                                (!leanh::lean_is_exclusive(v___x_2450_)) as u8;
                            if v_isSharedCheck_2517_ == 0 {
                                v___x_2512_ = v___x_2450_;
                                v_isShared_2513_ = v_isSharedCheck_2517_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2510_);
                                leanh::lean_dec(v___x_2450_);
                                v___x_2512_ = leanh::lean_box(0);
                                v_isShared_2513_ = v_isSharedCheck_2517_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_2436_);
                    leanh::lean_dec_ref(v_postNode_2435_);
                    leanh::lean_dec_ref(v_preNode_2434_);
                    v_isSharedCheck_2525_ = (!leanh::lean_is_exclusive(v_x_2437_)) as u8;
                    if v_isSharedCheck_2525_ == 0 {
                        v_unused_2526_ = leanh::lean_ctor_get(v_x_2437_, 0);
                        leanh::lean_dec(v_unused_2526_);
                        v___x_2519_ = v_x_2437_;
                        v_isShared_2520_ = v_isSharedCheck_2525_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2437_);
                        v___x_2519_ = leanh::lean_box(0);
                        v_isShared_2520_ = v_isSharedCheck_2525_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2456_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_2439_);
                leanh::lean_inc_ref(v___y_2438_);
                v___x_2457_ = leanh::lean_apply_7(
                    v_postNode_2435_,
                    v_val_2449_,
                    v_i_2447_,
                    v_children_2448_,
                    v___x_2456_,
                    v___y_2438_,
                    v___y_2439_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2457_) == 0 {
                    v_a_2458_ = leanh::lean_ctor_get(v___x_2457_, 0);
                    v_isSharedCheck_2468_ = (!leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2460_ = v___x_2457_;
                        v_isShared_2461_ = v_isSharedCheck_2468_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2458_);
                        leanh::lean_dec(v___x_2457_);
                        v___x_2460_ = leanh::lean_box(0);
                        v_isShared_2461_ = v_isSharedCheck_2468_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2454_);
                    v_a_2469_ = leanh::lean_ctor_get(v___x_2457_, 0);
                    v_isSharedCheck_2476_ = (!leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2471_ = v___x_2457_;
                        v_isShared_2472_ = v_isSharedCheck_2476_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2469_);
                        leanh::lean_dec(v___x_2457_);
                        v___x_2471_ = leanh::lean_box(0);
                        v_isShared_2472_ = v_isSharedCheck_2476_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2455_ == 0 {
                    leanh::lean_ctor_set(v___x_2454_, 0, v_a_2458_);
                    v___x_2463_ = v___x_2454_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2458_);
                    v___x_2463_ = v_reuseFailAlloc_2467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2461_ == 0 {
                    leanh::lean_ctor_set(v___x_2460_, 0, v___x_2463_);
                    v___x_2465_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
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
                    v_reuseFailAlloc_2475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2474_;
            }
            7 => {
                v___x_2489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2489_, 0, v_a_2485_);
                if v_isShared_2488_ == 0 {
                    leanh::lean_ctor_set(v___x_2487_, 0, v___x_2489_);
                    v___x_2491_ = v___x_2487_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
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
                    v_reuseFailAlloc_2500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
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
                    v_reuseFailAlloc_2508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
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
                    v_reuseFailAlloc_2516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
                    v___x_2515_ = v_reuseFailAlloc_2516_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2515_;
            }
            15 => {
                v___x_2521_ = leanh::lean_box(0);
                if v_isShared_2520_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2519_, 0);
                    leanh::lean_ctor_set(v___x_2519_, 0, v___x_2521_);
                    v___x_2523_ = v___x_2519_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
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
    mut v_preNode_2527_: *mut leanh::LeanObject,
    mut v_postNode_2528_: *mut leanh::LeanObject,
    mut v___x_2529_: *mut leanh::LeanObject,
    mut v_x_2530_: *mut leanh::LeanObject,
    mut v_x_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2530_) == 0 {
                    leanh::lean_dec(v___x_2529_);
                    leanh::lean_dec_ref(v_postNode_2528_);
                    leanh::lean_dec_ref(v_preNode_2527_);
                    v___x_2535_ = l_List_reverse___redArg(v_x_2531_);
                    v___x_2536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2536_, 0, v___x_2535_);
                    return v___x_2536_;
                } else {
                    v_head_2537_ = leanh::lean_ctor_get(v_x_2530_, 0);
                    v_tail_2538_ = leanh::lean_ctor_get(v_x_2530_, 1);
                    v_isSharedCheck_2556_ = (!leanh::lean_is_exclusive(v_x_2530_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2540_ = v_x_2530_;
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2538_);
                        leanh::lean_inc(v_head_2537_);
                        leanh::lean_dec(v_x_2530_);
                        v___x_2540_ = leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_2529_);
                leanh::lean_inc_ref(v_postNode_2528_);
                leanh::lean_inc_ref(v_preNode_2527_);
                v___x_2542_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2527_, v_postNode_2528_, v___x_2529_, v_head_2537_, v___y_2532_, v___y_2533_);
                if leanh::lean_obj_tag(v___x_2542_) == 0 {
                    v_a_2543_ = leanh::lean_ctor_get(v___x_2542_, 0);
                    leanh::lean_inc(v_a_2543_);
                    leanh::lean_dec_ref_known(v___x_2542_, 1);
                    if v_isShared_2541_ == 0 {
                        leanh::lean_ctor_set(v___x_2540_, 1, v_x_2531_);
                        leanh::lean_ctor_set(v___x_2540_, 0, v_a_2543_);
                        v___x_2545_ = v___x_2540_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2547_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2543_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_x_2531_);
                        v___x_2545_ = v_reuseFailAlloc_2547_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2540_);
                    leanh::lean_dec(v_tail_2538_);
                    leanh::lean_dec(v_x_2531_);
                    leanh::lean_dec(v___x_2529_);
                    leanh::lean_dec_ref(v_postNode_2528_);
                    leanh::lean_dec_ref(v_preNode_2527_);
                    v_a_2548_ = leanh::lean_ctor_get(v___x_2542_, 0);
                    v_isSharedCheck_2555_ = (!leanh::lean_is_exclusive(v___x_2542_)) as u8;
                    if v_isSharedCheck_2555_ == 0 {
                        v___x_2550_ = v___x_2542_;
                        v_isShared_2551_ = v_isSharedCheck_2555_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2548_);
                        leanh::lean_dec(v___x_2542_);
                        v___x_2550_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
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
    mut v_preNode_2557_: *mut leanh::LeanObject,
    mut v_postNode_2558_: *mut leanh::LeanObject,
    mut v___x_2559_: *mut leanh::LeanObject,
    mut v_x_2560_: *mut leanh::LeanObject,
    mut v_x_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
    mut v___y_2563_: *mut leanh::LeanObject,
    mut v___y_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2565_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_2557_, v_postNode_2558_, v___x_2559_, v_x_2560_, v_x_2561_, v___y_2562_, v___y_2563_);
    leanh::lean_dec(v___y_2563_);
    leanh::lean_dec_ref(v___y_2562_);
    return v_res_2565_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___boxed(
    mut v_preNode_2566_: *mut leanh::LeanObject,
    mut v_postNode_2567_: *mut leanh::LeanObject,
    mut v_x_2568_: *mut leanh::LeanObject,
    mut v_x_2569_: *mut leanh::LeanObject,
    mut v___y_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
    mut v___y_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2573_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2566_, v_postNode_2567_, v_x_2568_, v_x_2569_, v___y_2570_, v___y_2571_);
    leanh::lean_dec(v___y_2571_);
    leanh::lean_dec_ref(v___y_2570_);
    return v_res_2573_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(
    mut v_preNode_2574_: *mut leanh::LeanObject,
    mut v_postNode_2575_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2576_: *mut leanh::LeanObject,
    mut v_t_2577_: *mut leanh::LeanObject,
    mut v___y_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_unused_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2581_ = leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2581_, 0, v_postNode_2575_);
                v___x_2582_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_2574_, v___f_2581_, v_ctx_x3f_2576_, v_t_2577_, v___y_2578_, v___y_2579_);
                if leanh::lean_obj_tag(v___x_2582_) == 0 {
                    v_isSharedCheck_2590_ = (!leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v_unused_2591_ = leanh::lean_ctor_get(v___x_2582_, 0);
                        leanh::lean_dec(v_unused_2591_);
                        v___x_2584_ = v___x_2582_;
                        v_isShared_2585_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2582_);
                        v___x_2584_ = leanh::lean_box(0);
                        v_isShared_2585_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2592_ = leanh::lean_ctor_get(v___x_2582_, 0);
                    v_isSharedCheck_2599_ = (!leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2599_ == 0 {
                        v___x_2594_ = v___x_2582_;
                        v_isShared_2595_ = v_isSharedCheck_2599_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2592_);
                        leanh::lean_dec(v___x_2582_);
                        v___x_2594_ = leanh::lean_box(0);
                        v_isShared_2595_ = v_isSharedCheck_2599_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2586_ = leanh::lean_box(0);
                if v_isShared_2585_ == 0 {
                    leanh::lean_ctor_set(v___x_2584_, 0, v___x_2586_);
                    v___x_2588_ = v___x_2584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
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
                    v_reuseFailAlloc_2598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
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
    mut v_preNode_2600_: *mut leanh::LeanObject,
    mut v_postNode_2601_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2602_: *mut leanh::LeanObject,
    mut v_t_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_preNode_2600_, v_postNode_2601_, v_ctx_x3f_2602_, v_t_2603_, v___y_2604_, v___y_2605_);
    leanh::lean_dec(v___y_2605_);
    leanh::lean_dec_ref(v___y_2604_);
    return v_res_2607_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(
    mut v___y_2609_: u8,
    mut v_suppressElabErrors_2610_: u8,
    mut v_x_2611_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2611_) == 1 {
        let mut v_pre_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2612_ = leanh::lean_ctor_get(v_x_2611_, 0);
        if leanh::lean_obj_tag(v_pre_2612_) == 0 {
            let mut v_str_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2615_: u8 = 0;
            v_str_2613_ = leanh::lean_ctor_get(v_x_2611_, 1);
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
    mut v___y_2616_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2617_: *mut leanh::LeanObject,
    mut v_x_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_29418__boxed_2619_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2620_: u8 = 0;
    let mut v_res_2621_: u8 = 0;
    let mut v_r_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_29418__boxed_2619_ = (leanh::lean_unbox(v___y_2616_) as u8);
    v_suppressElabErrors_boxed_2620_ = (leanh::lean_unbox(v_suppressElabErrors_2617_) as u8);
    v_res_2621_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(v___y_29418__boxed_2619_, v_suppressElabErrors_boxed_2620_, v_x_2618_);
    leanh::lean_dec(v_x_2618_);
    v_r_2622_ = leanh::lean_box((v_res_2621_) as usize);
    return v_r_2622_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2623_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0);
    v___x_2625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2625_, 0, v___x_2624_);
    return v___x_2625_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
    v___x_2627_ = leanh::lean_unsigned_to_nat(0);
    v___x_2628_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2628_, 0, v___x_2627_);
    leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
    leanh::lean_ctor_set(v___x_2628_, 2, v___x_2627_);
    leanh::lean_ctor_set(v___x_2628_, 3, v___x_2627_);
    leanh::lean_ctor_set(v___x_2628_, 4, v___x_2626_);
    leanh::lean_ctor_set(v___x_2628_, 5, v___x_2626_);
    leanh::lean_ctor_set(v___x_2628_, 6, v___x_2626_);
    leanh::lean_ctor_set(v___x_2628_, 7, v___x_2626_);
    leanh::lean_ctor_set(v___x_2628_, 8, v___x_2626_);
    leanh::lean_ctor_set(v___x_2628_, 9, v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = leanh::lean_unsigned_to_nat(32);
    v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
    v___x_2631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2631_, 0, v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2632_: usize = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = 5usize;
    v___x_2633_ = leanh::lean_unsigned_to_nat(0);
    v___x_2634_ = leanh::lean_unsigned_to_nat(32);
    v___x_2635_ = lean_mk_empty_array_with_capacity(v___x_2634_);
    v___x_2636_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3);
    v___x_2637_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2637_, 0, v___x_2636_);
    leanh::lean_ctor_set(v___x_2637_, 1, v___x_2635_);
    leanh::lean_ctor_set(v___x_2637_, 2, v___x_2633_);
    leanh::lean_ctor_set(v___x_2637_, 3, v___x_2633_);
    leanh::lean_ctor_set_usize(v___x_2637_, 4, v___x_2632_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = leanh::lean_box(1);
    v___x_2639_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
    v___x_2640_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
    v___x_2641_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
    leanh::lean_ctor_set(v___x_2641_, 1, v___x_2639_);
    leanh::lean_ctor_set(v___x_2641_, 2, v___x_2638_);
    return v___x_2641_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(
    mut v_msgData_2642_: *mut leanh::LeanObject,
    mut v___y_2643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = lean_st_ref_get(v___y_2643_);
    v_env_2646_ = leanh::lean_ctor_get(v___x_2645_, 0);
    leanh::lean_inc_ref(v_env_2646_);
    leanh::lean_dec(v___x_2645_);
    v___x_2647_ = lean_st_ref_get(v___y_2643_);
    v_scopes_2648_ = leanh::lean_ctor_get(v___x_2647_, 2);
    leanh::lean_inc(v_scopes_2648_);
    leanh::lean_dec(v___x_2647_);
    v___x_2649_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2650_ = l_List_head_x21___redArg(v___x_2649_, v_scopes_2648_);
    leanh::lean_dec(v_scopes_2648_);
    v_opts_2651_ = leanh::lean_ctor_get(v___x_2650_, 1);
    leanh::lean_inc_ref(v_opts_2651_);
    leanh::lean_dec(v___x_2650_);
    v___x_2652_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2);
    v___x_2653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5);
    v___x_2654_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2654_, 0, v_env_2646_);
    leanh::lean_ctor_set(v___x_2654_, 1, v___x_2652_);
    leanh::lean_ctor_set(v___x_2654_, 2, v___x_2653_);
    leanh::lean_ctor_set(v___x_2654_, 3, v_opts_2651_);
    v___x_2655_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2655_, 0, v___x_2654_);
    leanh::lean_ctor_set(v___x_2655_, 1, v_msgData_2642_);
    v___x_2656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2656_, 0, v___x_2655_);
    return v___x_2656_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___boxed(
    mut v_msgData_2657_: *mut leanh::LeanObject,
    mut v___y_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2660_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_2657_, v___y_2658_);
    leanh::lean_dec(v___y_2658_);
    return v_res_2660_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(
    mut v_ref_2662_: *mut leanh::LeanObject,
    mut v_msgData_2663_: *mut leanh::LeanObject,
    mut v_severity_2664_: u8,
    mut v_isSilent_2665_: u8,
    mut v___y_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: u8 = 0;
    let mut v___y_2674_: u8 = 0;
    let mut v___y_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_a_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_a_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v___y_2733_: u8 = 0;
    let mut v___y_2734_: u8 = 0;
    let mut v___y_2735_: u8 = 0;
    let mut v___y_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2740_: u8 = 0;
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v___y_2761_: u8 = 0;
    let mut v___y_2762_: u8 = 0;
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: u8 = 0;
    let mut v___y_2770_: u8 = 0;
    let mut v___y_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v___x_2786_: u8 = 0;
    let mut v___y_2788_: u8 = 0;
    let mut v___y_2789_: u8 = 0;
    let mut v___y_2790_: u8 = 0;
    let mut v___y_2792_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc_ref(v_msgData_2663_);
                    v___x_2805_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2663_);
                    v___y_2792_ = v___x_2805_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2678_ = l_Lean_Elab_Command_getScope___redArg(v___y_2677_);
                if leanh::lean_obj_tag(v___x_2678_) == 0 {
                    v_a_2679_ = leanh::lean_ctor_get(v___x_2678_, 0);
                    leanh::lean_inc(v_a_2679_);
                    leanh::lean_dec_ref_known(v___x_2678_, 1);
                    v___x_2680_ = l_Lean_Elab_Command_getScope___redArg(v___y_2677_);
                    if leanh::lean_obj_tag(v___x_2680_) == 0 {
                        v_a_2681_ = leanh::lean_ctor_get(v___x_2680_, 0);
                        v_isSharedCheck_2715_ =
                            (!leanh::lean_is_exclusive(v___x_2680_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2683_ = v___x_2680_;
                            v_isShared_2684_ = v_isSharedCheck_2715_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2681_);
                            leanh::lean_dec(v___x_2680_);
                            v___x_2683_ = leanh::lean_box(0);
                            v_isShared_2684_ = v_isSharedCheck_2715_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2679_);
                        leanh::lean_dec_ref(v___y_2675_);
                        leanh::lean_dec(v___y_2672_);
                        leanh::lean_dec_ref(v___y_2670_);
                        v_a_2716_ = leanh::lean_ctor_get(v___x_2680_, 0);
                        v_isSharedCheck_2723_ =
                            (!leanh::lean_is_exclusive(v___x_2680_)) as u8;
                        if v_isSharedCheck_2723_ == 0 {
                            v___x_2718_ = v___x_2680_;
                            v_isShared_2719_ = v_isSharedCheck_2723_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2716_);
                            leanh::lean_dec(v___x_2680_);
                            v___x_2718_ = leanh::lean_box(0);
                            v_isShared_2719_ = v_isSharedCheck_2723_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2675_);
                    leanh::lean_dec(v___y_2672_);
                    leanh::lean_dec_ref(v___y_2670_);
                    v_a_2724_ = leanh::lean_ctor_get(v___x_2678_, 0);
                    v_isSharedCheck_2731_ = (!leanh::lean_is_exclusive(v___x_2678_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2726_ = v___x_2678_;
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2724_);
                        leanh::lean_dec(v___x_2678_);
                        v___x_2726_ = leanh::lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = lean_st_ref_take(v___y_2677_);
                v_currNamespace_2686_ = leanh::lean_ctor_get(v_a_2679_, 2);
                leanh::lean_inc(v_currNamespace_2686_);
                leanh::lean_dec(v_a_2679_);
                v_openDecls_2687_ = leanh::lean_ctor_get(v_a_2681_, 3);
                leanh::lean_inc(v_openDecls_2687_);
                leanh::lean_dec(v_a_2681_);
                v_env_2688_ = leanh::lean_ctor_get(v___x_2685_, 0);
                v_messages_2689_ = leanh::lean_ctor_get(v___x_2685_, 1);
                v_scopes_2690_ = leanh::lean_ctor_get(v___x_2685_, 2);
                v_usedQuotCtxts_2691_ = leanh::lean_ctor_get(v___x_2685_, 3);
                v_nextMacroScope_2692_ = leanh::lean_ctor_get(v___x_2685_, 4);
                v_maxRecDepth_2693_ = leanh::lean_ctor_get(v___x_2685_, 5);
                v_ngen_2694_ = leanh::lean_ctor_get(v___x_2685_, 6);
                v_auxDeclNGen_2695_ = leanh::lean_ctor_get(v___x_2685_, 7);
                v_infoState_2696_ = leanh::lean_ctor_get(v___x_2685_, 8);
                v_traceState_2697_ = leanh::lean_ctor_get(v___x_2685_, 9);
                v_snapshotTasks_2698_ = leanh::lean_ctor_get(v___x_2685_, 10);
                v_isSharedCheck_2714_ = (!leanh::lean_is_exclusive(v___x_2685_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2700_ = v___x_2685_;
                    v_isShared_2701_ = v_isSharedCheck_2714_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2698_);
                    leanh::lean_inc(v_traceState_2697_);
                    leanh::lean_inc(v_infoState_2696_);
                    leanh::lean_inc(v_auxDeclNGen_2695_);
                    leanh::lean_inc(v_ngen_2694_);
                    leanh::lean_inc(v_maxRecDepth_2693_);
                    leanh::lean_inc(v_nextMacroScope_2692_);
                    leanh::lean_inc(v_usedQuotCtxts_2691_);
                    leanh::lean_inc(v_scopes_2690_);
                    leanh::lean_inc(v_messages_2689_);
                    leanh::lean_inc(v_env_2688_);
                    leanh::lean_dec(v___x_2685_);
                    v___x_2700_ = leanh::lean_box(0);
                    v_isShared_2701_ = v_isSharedCheck_2714_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2702_, 0, v_currNamespace_2686_);
                leanh::lean_ctor_set(v___x_2702_, 1, v_openDecls_2687_);
                v___x_2703_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
                leanh::lean_ctor_set(v___x_2703_, 1, v___y_2675_);
                leanh::lean_inc_ref(v___y_2671_);
                leanh::lean_inc_ref(v___y_2676_);
                v___x_2704_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2704_, 0, v___y_2676_);
                leanh::lean_ctor_set(v___x_2704_, 1, v___y_2670_);
                leanh::lean_ctor_set(v___x_2704_, 2, v___y_2672_);
                leanh::lean_ctor_set(v___x_2704_, 3, v___y_2671_);
                leanh::lean_ctor_set(v___x_2704_, 4, v___x_2703_);
                leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2674_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2673_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2704_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2665_,
                );
                v___x_2705_ = l_Lean_MessageLog_add(v___x_2704_, v_messages_2689_);
                if v_isShared_2701_ == 0 {
                    leanh::lean_ctor_set(v___x_2700_, 1, v___x_2705_);
                    v___x_2707_ = v___x_2700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_env_2688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 2, v_scopes_2690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 3, v_usedQuotCtxts_2691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_nextMacroScope_2692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 5, v_maxRecDepth_2693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 6, v_ngen_2694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 7, v_auxDeclNGen_2695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 8, v_infoState_2696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 9, v_traceState_2697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 10, v_snapshotTasks_2698_);
                    v___x_2707_ = v_reuseFailAlloc_2713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2708_ = lean_st_ref_set(v___y_2677_, v___x_2707_);
                v___x_2709_ = leanh::lean_box(0);
                if v_isShared_2684_ == 0 {
                    leanh::lean_ctor_set(v___x_2683_, 0, v___x_2709_);
                    v___x_2711_ = v___x_2683_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
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
                    v_reuseFailAlloc_2722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
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
                    v_reuseFailAlloc_2730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2729_;
            }
            10 => {
                v_fileName_2738_ = leanh::lean_ctor_get(v___y_2666_, 0);
                v_fileMap_2739_ = leanh::lean_ctor_get(v___y_2666_, 1);
                v_suppressElabErrors_2740_ = leanh::lean_ctor_get_uint8(
                    v___y_2666_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v___x_2741_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2663_,
                    );
                v___x_2742_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v___x_2741_, v___y_2667_);
                v_a_2743_ = leanh::lean_ctor_get(v___x_2742_, 0);
                v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v___x_2742_)) as u8;
                if v_isSharedCheck_2759_ == 0 {
                    v___x_2745_ = v___x_2742_;
                    v_isShared_2746_ = v_isSharedCheck_2759_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2743_);
                    leanh::lean_dec(v___x_2742_);
                    v___x_2745_ = leanh::lean_box(0);
                    v_isShared_2746_ = v_isSharedCheck_2759_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc_ref_n(v_fileMap_2739_, 2);
                v___x_2747_ = l_Lean_FileMap_toPosition(v_fileMap_2739_, v___y_2736_);
                leanh::lean_dec(v___y_2736_);
                v___x_2748_ = l_Lean_FileMap_toPosition(v_fileMap_2739_, v___y_2737_);
                leanh::lean_dec(v___y_2737_);
                v___x_2749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
                v___x_2750_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0;
                if v_suppressElabErrors_2740_ == 0 {
                    leanh::lean_del_object(v___x_2745_);
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
                    v___x_2751_ = leanh::lean_box((v___y_2733_) as usize);
                    v___x_2752_ = leanh::lean_box((v_suppressElabErrors_2740_) as usize);
                    v___f_2753_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2753_, 0, v___x_2751_);
                    leanh::lean_closure_set(v___f_2753_, 1, v___x_2752_);
                    leanh::lean_inc(v_a_2743_);
                    v___x_2754_ = l_Lean_MessageData_hasTag(v___f_2753_, v_a_2743_);
                    if v___x_2754_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2749_, 1);
                        leanh::lean_dec_ref(v___x_2747_);
                        leanh::lean_dec(v_a_2743_);
                        v___x_2755_ = leanh::lean_box(0);
                        if v_isShared_2746_ == 0 {
                            leanh::lean_ctor_set(v___x_2745_, 0, v___x_2755_);
                            v___x_2757_ = v___x_2745_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2758_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
                            v___x_2757_ = v_reuseFailAlloc_2758_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2745_);
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
                leanh::lean_dec(v___y_2764_);
                if leanh::lean_obj_tag(v___x_2766_) == 0 {
                    leanh::lean_inc(v___y_2765_);
                    v___y_2733_ = v___y_2761_;
                    v___y_2734_ = v___y_2762_;
                    v___y_2735_ = v___y_2763_;
                    v___y_2736_ = v___y_2765_;
                    v___y_2737_ = v___y_2765_;
                    state = 10;
                    continue;
                } else {
                    v_val_2767_ = leanh::lean_ctor_get(v___x_2766_, 0);
                    leanh::lean_inc(v_val_2767_);
                    leanh::lean_dec_ref_known(v___x_2766_, 1);
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
                if leanh::lean_obj_tag(v___x_2772_) == 0 {
                    v_a_2773_ = leanh::lean_ctor_get(v___x_2772_, 0);
                    leanh::lean_inc(v_a_2773_);
                    leanh::lean_dec_ref_known(v___x_2772_, 1);
                    v_ref_2774_ = l_Lean_replaceRef(v_ref_2662_, v_a_2773_);
                    leanh::lean_dec(v_a_2773_);
                    v___x_2775_ = l_Lean_Syntax_getPos_x3f(v_ref_2774_, v___y_2770_);
                    if leanh::lean_obj_tag(v___x_2775_) == 0 {
                        v___x_2776_ = leanh::lean_unsigned_to_nat(0);
                        v___y_2761_ = v___y_2769_;
                        v___y_2762_ = v___y_2771_;
                        v___y_2763_ = v___y_2770_;
                        v___y_2764_ = v_ref_2774_;
                        v___y_2765_ = v___x_2776_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2777_ = leanh::lean_ctor_get(v___x_2775_, 0);
                        leanh::lean_inc(v_val_2777_);
                        leanh::lean_dec_ref_known(v___x_2775_, 1);
                        v___y_2761_ = v___y_2769_;
                        v___y_2762_ = v___y_2771_;
                        v___y_2763_ = v___y_2770_;
                        v___y_2764_ = v_ref_2774_;
                        v___y_2765_ = v_val_2777_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2663_);
                    v_a_2778_ = leanh::lean_ctor_get(v___x_2772_, 0);
                    v_isSharedCheck_2785_ = (!leanh::lean_is_exclusive(v___x_2772_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2780_ = v___x_2772_;
                        v_isShared_2781_ = v_isSharedCheck_2785_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2778_);
                        leanh::lean_dec(v___x_2772_);
                        v___x_2780_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
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
                    v_scopes_2794_ = leanh::lean_ctor_get(v___x_2793_, 2);
                    leanh::lean_inc(v_scopes_2794_);
                    leanh::lean_dec(v___x_2793_);
                    v___x_2795_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2796_ = l_List_head_x21___redArg(v___x_2795_, v_scopes_2794_);
                    leanh::lean_dec(v_scopes_2794_);
                    v_opts_2797_ = leanh::lean_ctor_get(v___x_2796_, 1);
                    leanh::lean_inc_ref(v_opts_2797_);
                    leanh::lean_dec(v___x_2796_);
                    v___x_2798_ = 1;
                    v___x_2799_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2664_, v___x_2798_);
                    if v___x_2799_ == 0 {
                        leanh::lean_dec_ref(v_opts_2797_);
                        v___y_2788_ = v___y_2792_;
                        v___y_2789_ = v___y_2792_;
                        v___y_2790_ = v___x_2799_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2800_ = l_Lean_warningAsError;
                        v___x_2801_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_2797_, v___x_2800_);
                        leanh::lean_dec_ref(v_opts_2797_);
                        v___y_2788_ = v___y_2792_;
                        v___y_2789_ = v___y_2792_;
                        v___y_2790_ = v___x_2801_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2663_);
                    v___x_2802_ = leanh::lean_box(0);
                    v___x_2803_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2803_, 0, v___x_2802_);
                    return v___x_2803_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___boxed(
    mut v_ref_2806_: *mut leanh::LeanObject,
    mut v_msgData_2807_: *mut leanh::LeanObject,
    mut v_severity_2808_: *mut leanh::LeanObject,
    mut v_isSilent_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2813_: u8 = 0;
    let mut v_isSilent_boxed_2814_: u8 = 0;
    let mut v_res_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2813_ = (leanh::lean_unbox(v_severity_2808_) as u8);
    v_isSilent_boxed_2814_ = (leanh::lean_unbox(v_isSilent_2809_) as u8);
    v_res_2815_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_2806_, v_msgData_2807_, v_severity_boxed_2813_, v_isSilent_boxed_2814_, v___y_2810_, v___y_2811_);
    leanh::lean_dec(v___y_2811_);
    leanh::lean_dec_ref(v___y_2810_);
    leanh::lean_dec(v_ref_2806_);
    return v_res_2815_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(
    mut v_ref_2816_: *mut leanh::LeanObject,
    mut v_msgData_2817_: *mut leanh::LeanObject,
    mut v___y_2818_: *mut leanh::LeanObject,
    mut v___y_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = 1;
    v___x_2822_ = 0;
    v___x_2823_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_2816_, v_msgData_2817_, v___x_2821_, v___x_2822_, v___y_2818_, v___y_2819_);
    return v___x_2823_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15___boxed(
    mut v_ref_2824_: *mut leanh::LeanObject,
    mut v_msgData_2825_: *mut leanh::LeanObject,
    mut v___y_2826_: *mut leanh::LeanObject,
    mut v___y_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_ref_2824_, v_msgData_2825_, v___y_2826_, v___y_2827_);
    leanh::lean_dec(v___y_2827_);
    leanh::lean_dec_ref(v___y_2826_);
    leanh::lean_dec(v_ref_2824_);
    return v_res_2829_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0;
    v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
    return v___x_2832_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2;
    v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
    return v___x_2835_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(
    mut v_linterOption_2836_: *mut leanh::LeanObject,
    mut v_stx_2837_: *mut leanh::LeanObject,
    mut v_msg_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_unused_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2842_ = leanh::lean_ctor_get(v_linterOption_2836_, 0);
                v_isSharedCheck_2859_ =
                    (!leanh::lean_is_exclusive(v_linterOption_2836_)) as u8;
                if v_isSharedCheck_2859_ == 0 {
                    v_unused_2860_ = leanh::lean_ctor_get(v_linterOption_2836_, 1);
                    leanh::lean_dec(v_unused_2860_);
                    v___x_2844_ = v_linterOption_2836_;
                    v_isShared_2845_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_2842_);
                    leanh::lean_dec(v_linterOption_2836_);
                    v___x_2844_ = leanh::lean_box(0);
                    v_isShared_2845_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2846_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1);
                leanh::lean_inc(v_name_2842_);
                v___x_2847_ = l_Lean_MessageData_ofName(v_name_2842_);
                if v_isShared_2845_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2844_, 7);
                    leanh::lean_ctor_set(v___x_2844_, 1, v___x_2847_);
                    leanh::lean_ctor_set(v___x_2844_, 0, v___x_2846_);
                    v___x_2849_ = v___x_2844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2847_);
                    v___x_2849_ = v_reuseFailAlloc_2858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2850_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3);
                v___x_2851_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2851_, 0, v___x_2849_);
                leanh::lean_ctor_set(v___x_2851_, 1, v___x_2850_);
                v_disable_2852_ = l_Lean_MessageData_note(v___x_2851_);
                v___x_2853_ = l_Lean_Linter_linterMessageTag;
                v___x_2854_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2854_, 0, v_msg_2838_);
                leanh::lean_ctor_set(v___x_2854_, 1, v_disable_2852_);
                v___x_2855_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2855_, 0, v___x_2853_);
                leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
                v___x_2856_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2856_, 0, v_name_2842_);
                leanh::lean_ctor_set(v___x_2856_, 1, v___x_2855_);
                v___x_2857_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_stx_2837_, v___x_2856_, v___y_2839_, v___y_2840_);
                return v___x_2857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(
    mut v_linterOption_2861_: *mut leanh::LeanObject,
    mut v_stx_2862_: *mut leanh::LeanObject,
    mut v_msg_2863_: *mut leanh::LeanObject,
    mut v___y_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
    mut v___y_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2867_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_linterOption_2861_, v_stx_2862_, v_msg_2863_, v___y_2864_, v___y_2865_);
    leanh::lean_dec(v___y_2865_);
    leanh::lean_dec_ref(v___y_2864_);
    leanh::lean_dec(v_stx_2862_);
    return v_res_2867_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2868_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0);
    v___x_2870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    return v___x_2870_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = leanh::lean_box(1);
    v___x_2872_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
    v___x_2873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1);
    v___x_2874_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
    leanh::lean_ctor_set(v___x_2874_, 1, v___x_2872_);
    leanh::lean_ctor_set(v___x_2874_, 2, v___x_2871_);
    return v___x_2874_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(
    mut v_val_2877_: *mut leanh::LeanObject,
    mut v_a_2878_: u8,
    mut v___x_2879_: *mut leanh::LeanObject,
    mut v___f_2880_: *mut leanh::LeanObject,
    mut v_ci_2881_: *mut leanh::LeanObject,
    mut v_info_2882_: *mut leanh::LeanObject,
    mut v_x_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v_toCommandContextInfo_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v_parentDecl_x3f_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2898_: u8 = 0;
    let mut v_env_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_toElabInfo_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctxBefore_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctxAfter_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v_val_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2929_: u8 = 0;
    let mut v_a_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v_ref_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_unused_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_unused_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2887_ = lean_st_ref_get(v_val_2877_);
                v___x_2888_ = (leanh::lean_unbox(v___x_2887_) as u8);
                leanh::lean_dec(v___x_2887_);
                if v___x_2888_ == 0 {
                    if leanh::lean_obj_tag(v_info_2882_) == 0 {
                        v_toCommandContextInfo_2889_ = leanh::lean_ctor_get(v_ci_2881_, 0);
                        leanh::lean_inc_ref(v_toCommandContextInfo_2889_);
                        v_i_2890_ = leanh::lean_ctor_get(v_info_2882_, 0);
                        v_isSharedCheck_2965_ =
                            (!leanh::lean_is_exclusive(v_info_2882_)) as u8;
                        if v_isSharedCheck_2965_ == 0 {
                            v___x_2892_ = v_info_2882_;
                            v_isShared_2893_ = v_isSharedCheck_2965_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_i_2890_);
                            leanh::lean_dec(v_info_2882_);
                            v___x_2892_ = leanh::lean_box(0);
                            v_isShared_2893_ = v_isSharedCheck_2965_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_info_2882_);
                        leanh::lean_dec_ref(v_ci_2881_);
                        leanh::lean_dec_ref(v___f_2880_);
                        leanh::lean_dec_ref(v___x_2879_);
                        v___x_2966_ = leanh::lean_box(0);
                        v___x_2967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                        return v___x_2967_;
                    }
                } else {
                    leanh::lean_dec_ref(v_info_2882_);
                    leanh::lean_dec_ref(v_ci_2881_);
                    leanh::lean_dec_ref(v___f_2880_);
                    leanh::lean_dec_ref(v___x_2879_);
                    v___x_2968_ = leanh::lean_box(0);
                    v___x_2969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                    return v___x_2969_;
                }
            }
            1 => {
                v_parentDecl_x3f_2894_ = leanh::lean_ctor_get(v_ci_2881_, 1);
                v_autoImplicits_2895_ = leanh::lean_ctor_get(v_ci_2881_, 2);
                v_isSharedCheck_2963_ = (!leanh::lean_is_exclusive(v_ci_2881_)) as u8;
                if v_isSharedCheck_2963_ == 0 {
                    v_unused_2964_ = leanh::lean_ctor_get(v_ci_2881_, 0);
                    leanh::lean_dec(v_unused_2964_);
                    v___x_2897_ = v_ci_2881_;
                    v_isShared_2898_ = v_isSharedCheck_2963_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_autoImplicits_2895_);
                    leanh::lean_inc(v_parentDecl_x3f_2894_);
                    leanh::lean_dec(v_ci_2881_);
                    v___x_2897_ = leanh::lean_box(0);
                    v_isShared_2898_ = v_isSharedCheck_2963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_env_2899_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 0);
                v_cmdEnv_x3f_2900_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 1);
                v_fileMap_2901_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 2);
                v_options_2902_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 4);
                v_currNamespace_2903_ =
                    leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 5);
                v_openDecls_2904_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 6);
                v_ngen_2905_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 7);
                v_isSharedCheck_2961_ =
                    (!leanh::lean_is_exclusive(v_toCommandContextInfo_2889_)) as u8;
                if v_isSharedCheck_2961_ == 0 {
                    v_unused_2962_ = leanh::lean_ctor_get(v_toCommandContextInfo_2889_, 3);
                    leanh::lean_dec(v_unused_2962_);
                    v___x_2907_ = v_toCommandContextInfo_2889_;
                    v_isShared_2908_ = v_isSharedCheck_2961_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_ngen_2905_);
                    leanh::lean_inc(v_openDecls_2904_);
                    leanh::lean_inc(v_currNamespace_2903_);
                    leanh::lean_inc(v_options_2902_);
                    leanh::lean_inc(v_fileMap_2901_);
                    leanh::lean_inc(v_cmdEnv_x3f_2900_);
                    leanh::lean_inc(v_env_2899_);
                    leanh::lean_dec(v_toCommandContextInfo_2889_);
                    v___x_2907_ = leanh::lean_box(0);
                    v_isShared_2908_ = v_isSharedCheck_2961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toElabInfo_2909_ = leanh::lean_ctor_get(v_i_2890_, 0);
                leanh::lean_inc_ref(v_toElabInfo_2909_);
                v_mctxBefore_2910_ = leanh::lean_ctor_get(v_i_2890_, 1);
                leanh::lean_inc_ref(v_mctxBefore_2910_);
                v_goalsBefore_2911_ = leanh::lean_ctor_get(v_i_2890_, 2);
                leanh::lean_inc(v_goalsBefore_2911_);
                v_mctxAfter_2912_ = leanh::lean_ctor_get(v_i_2890_, 3);
                leanh::lean_inc_ref(v_mctxAfter_2912_);
                v_goalsAfter_2913_ = leanh::lean_ctor_get(v_i_2890_, 4);
                leanh::lean_inc(v_goalsAfter_2913_);
                leanh::lean_dec_ref(v_i_2890_);
                leanh::lean_inc_ref(v_ngen_2905_);
                leanh::lean_inc(v_openDecls_2904_);
                leanh::lean_inc(v_currNamespace_2903_);
                leanh::lean_inc_ref(v_options_2902_);
                leanh::lean_inc_ref(v_fileMap_2901_);
                leanh::lean_inc(v_cmdEnv_x3f_2900_);
                leanh::lean_inc_ref(v_env_2899_);
                if v_isShared_2908_ == 0 {
                    leanh::lean_ctor_set(v___x_2907_, 3, v_mctxBefore_2910_);
                    v___x_2946_ = v___x_2907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_env_2899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_cmdEnv_x3f_2900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_fileMap_2901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_mctxBefore_2910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_options_2902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_currNamespace_2903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 6, v_openDecls_2904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 7, v_ngen_2905_);
                    v___x_2946_ = v_reuseFailAlloc_2960_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                if leanh::lean_obj_tag(v___y_2915_) == 0 {
                    leanh::lean_del_object(v___x_2892_);
                    v_a_2916_ = leanh::lean_ctor_get(v___y_2915_, 0);
                    v_isSharedCheck_2929_ = (!leanh::lean_is_exclusive(v___y_2915_)) as u8;
                    if v_isSharedCheck_2929_ == 0 {
                        v___x_2918_ = v___y_2915_;
                        v_isShared_2919_ = v_isSharedCheck_2929_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2916_);
                        leanh::lean_dec(v___y_2915_);
                        v___x_2918_ = leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2929_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_toElabInfo_2909_);
                    leanh::lean_dec_ref(v___x_2879_);
                    v_a_2930_ = leanh::lean_ctor_get(v___y_2915_, 0);
                    v_isSharedCheck_2944_ = (!leanh::lean_is_exclusive(v___y_2915_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2932_ = v___y_2915_;
                        v_isShared_2933_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2930_);
                        leanh::lean_dec(v___y_2915_);
                        v___x_2932_ = leanh::lean_box(0);
                        v_isShared_2933_ = v_isSharedCheck_2944_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2916_) == 1 {
                    leanh::lean_del_object(v___x_2918_);
                    v_val_2920_ = leanh::lean_ctor_get(v_a_2916_, 0);
                    leanh::lean_inc(v_val_2920_);
                    leanh::lean_dec_ref_known(v_a_2916_, 1);
                    v___x_2921_ = leanh::lean_box((v_a_2878_) as usize);
                    v___x_2922_ = lean_st_ref_set(v_val_2877_, v___x_2921_);
                    v_stx_2923_ = leanh::lean_ctor_get(v_toElabInfo_2909_, 1);
                    leanh::lean_inc(v_stx_2923_);
                    leanh::lean_dec_ref(v_toElabInfo_2909_);
                    v___x_2924_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___x_2879_, v_stx_2923_, v_val_2920_, v___y_2884_, v___y_2885_);
                    leanh::lean_dec(v_stx_2923_);
                    return v___x_2924_;
                } else {
                    leanh::lean_dec(v_a_2916_);
                    leanh::lean_dec_ref(v_toElabInfo_2909_);
                    leanh::lean_dec_ref(v___x_2879_);
                    v___x_2925_ = leanh::lean_box(0);
                    if v_isShared_2919_ == 0 {
                        leanh::lean_ctor_set(v___x_2918_, 0, v___x_2925_);
                        v___x_2927_ = v___x_2918_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
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
                v_ref_2934_ = leanh::lean_ctor_get(v___y_2884_, 7);
                v___x_2935_ = lean_io_error_to_string(v_a_2930_);
                if v_isShared_2893_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2892_, 3);
                    leanh::lean_ctor_set(v___x_2892_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2892_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2935_);
                    v___x_2937_ = v_reuseFailAlloc_2943_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2938_ = l_Lean_MessageData_ofFormat(v___x_2937_);
                leanh::lean_inc(v_ref_2934_);
                v___x_2939_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2939_, 0, v_ref_2934_);
                leanh::lean_ctor_set(v___x_2939_, 1, v___x_2938_);
                if v_isShared_2933_ == 0 {
                    leanh::lean_ctor_set(v___x_2932_, 0, v___x_2939_);
                    v___x_2941_ = v___x_2932_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2941_;
            }
            10 => {
                leanh::lean_inc_ref(v_autoImplicits_2895_);
                leanh::lean_inc(v_parentDecl_x3f_2894_);
                if v_isShared_2898_ == 0 {
                    leanh::lean_ctor_set(v___x_2897_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2897_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_parentDecl_x3f_2894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_autoImplicits_2895_);
                    v___x_2948_ = v_reuseFailAlloc_2959_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2949_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2);
                v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3;
                leanh::lean_inc_ref(v___f_2880_);
                v___x_2951_ =
                    leanh::lean_apply_2(v___f_2880_, v___x_2950_, v_goalsBefore_2911_);
                v___x_2952_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                    v___x_2948_,
                    v___x_2949_,
                    v___x_2951_,
                );
                if leanh::lean_obj_tag(v___x_2952_) == 0 {
                    v_a_2953_ = leanh::lean_ctor_get(v___x_2952_, 0);
                    leanh::lean_inc(v_a_2953_);
                    if leanh::lean_obj_tag(v_a_2953_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2952_, 1);
                        v___x_2954_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                        leanh::lean_ctor_set(v___x_2954_, 0, v_env_2899_);
                        leanh::lean_ctor_set(v___x_2954_, 1, v_cmdEnv_x3f_2900_);
                        leanh::lean_ctor_set(v___x_2954_, 2, v_fileMap_2901_);
                        leanh::lean_ctor_set(v___x_2954_, 3, v_mctxAfter_2912_);
                        leanh::lean_ctor_set(v___x_2954_, 4, v_options_2902_);
                        leanh::lean_ctor_set(v___x_2954_, 5, v_currNamespace_2903_);
                        leanh::lean_ctor_set(v___x_2954_, 6, v_openDecls_2904_);
                        leanh::lean_ctor_set(v___x_2954_, 7, v_ngen_2905_);
                        v___x_2955_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2955_, 0, v___x_2954_);
                        leanh::lean_ctor_set(v___x_2955_, 1, v_parentDecl_x3f_2894_);
                        leanh::lean_ctor_set(v___x_2955_, 2, v_autoImplicits_2895_);
                        v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4;
                        v___x_2957_ = leanh::lean_apply_2(
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
                        leanh::lean_dec_ref_known(v_a_2953_, 1);
                        leanh::lean_dec(v_goalsAfter_2913_);
                        leanh::lean_dec_ref(v_mctxAfter_2912_);
                        leanh::lean_dec_ref(v_ngen_2905_);
                        leanh::lean_dec(v_openDecls_2904_);
                        leanh::lean_dec(v_currNamespace_2903_);
                        leanh::lean_dec_ref(v_options_2902_);
                        leanh::lean_dec_ref(v_fileMap_2901_);
                        leanh::lean_dec(v_cmdEnv_x3f_2900_);
                        leanh::lean_dec_ref(v_env_2899_);
                        leanh::lean_dec_ref(v_autoImplicits_2895_);
                        leanh::lean_dec(v_parentDecl_x3f_2894_);
                        leanh::lean_dec_ref(v___f_2880_);
                        v___y_2915_ = v___x_2952_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_goalsAfter_2913_);
                    leanh::lean_dec_ref(v_mctxAfter_2912_);
                    leanh::lean_dec_ref(v_ngen_2905_);
                    leanh::lean_dec(v_openDecls_2904_);
                    leanh::lean_dec(v_currNamespace_2903_);
                    leanh::lean_dec_ref(v_options_2902_);
                    leanh::lean_dec_ref(v_fileMap_2901_);
                    leanh::lean_dec(v_cmdEnv_x3f_2900_);
                    leanh::lean_dec_ref(v_env_2899_);
                    leanh::lean_dec_ref(v_autoImplicits_2895_);
                    leanh::lean_dec(v_parentDecl_x3f_2894_);
                    leanh::lean_dec_ref(v___f_2880_);
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
    mut v_val_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v___x_2972_: *mut leanh::LeanObject,
    mut v___f_2973_: *mut leanh::LeanObject,
    mut v_ci_2974_: *mut leanh::LeanObject,
    mut v_info_2975_: *mut leanh::LeanObject,
    mut v_x_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
    mut v___y_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_29890__boxed_2980_: u8 = 0;
    let mut v_res_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_29890__boxed_2980_ = (leanh::lean_unbox(v_a_2971_) as u8);
    v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(v_val_2970_, v_a_29890__boxed_2980_, v___x_2972_, v___f_2973_, v_ci_2974_, v_info_2975_, v_x_2976_, v___y_2977_, v___y_2978_);
    leanh::lean_dec(v___y_2978_);
    leanh::lean_dec_ref(v___y_2977_);
    leanh::lean_dec_ref(v_x_2976_);
    leanh::lean_dec(v_val_2970_);
    return v_res_2981_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(
    mut v___x_2982_: *mut leanh::LeanObject,
    mut v_a_2983_: *mut leanh::LeanObject,
    mut v_a_2984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2993_: u8 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2983_) == 0 {
                    leanh::lean_dec_ref(v___x_2982_);
                    v___x_2985_ = lean_array_to_list(v_a_2984_);
                    return v___x_2985_;
                } else {
                    v_head_2986_ = leanh::lean_ctor_get(v_a_2983_, 0);
                    leanh::lean_inc(v_head_2986_);
                    v_tail_2987_ = leanh::lean_ctor_get(v_a_2983_, 1);
                    leanh::lean_inc(v_tail_2987_);
                    leanh::lean_dec_ref_known(v_a_2983_, 2);
                    v_fst_2988_ = leanh::lean_ctor_get(v_head_2986_, 0);
                    leanh::lean_inc(v_fst_2988_);
                    v_snd_2989_ = leanh::lean_ctor_get(v_head_2986_, 1);
                    leanh::lean_inc(v_snd_2989_);
                    leanh::lean_dec(v_head_2986_);
                    v___x_2990_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2991_ = lean_nat_dec_lt(v___x_2990_, v_snd_2989_);
                    leanh::lean_dec(v_snd_2989_);
                    if v___x_2991_ == 0 {
                        leanh::lean_dec(v_fst_2988_);
                        v_a_2983_ = v_tail_2987_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2988_);
                        leanh::lean_inc_ref(v___x_2982_);
                        v___x_2993_ = lean_get_reducibility_status(v___x_2982_, v_fst_2988_);
                        if v___x_2993_ == 1 {
                            leanh::lean_inc_ref(v___x_2982_);
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
                                leanh::lean_dec(v_fst_2988_);
                                v_a_2983_ = v_tail_2987_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_2988_);
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
    mut v_o_3002_: *mut leanh::LeanObject,
    mut v_k_3003_: *mut leanh::LeanObject,
    mut v_v_3004_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3006_: u8 = 0;
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3005_ = leanh::lean_ctor_get(v_o_3002_, 0);
                v_hasTrace_3006_ = leanh::lean_ctor_get_uint8(
                    v_o_3002_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3020_ = (!leanh::lean_is_exclusive(v_o_3002_)) as u8;
                if v_isSharedCheck_3020_ == 0 {
                    v___x_3008_ = v_o_3002_;
                    v_isShared_3009_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3005_);
                    leanh::lean_dec(v_o_3002_);
                    v___x_3008_ = leanh::lean_box(0);
                    v_isShared_3009_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3010_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3010_, 0 as u32, v_v_3004_);
                leanh::lean_inc(v_k_3003_);
                v___x_3011_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3003_, v___x_3010_, v_map_3005_);
                if v_hasTrace_3006_ == 0 {
                    v___x_3012_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0;
                    v___x_3013_ = l_Lean_Name_isPrefixOf(v___x_3012_, v_k_3003_);
                    leanh::lean_dec(v_k_3003_);
                    if v_isShared_3009_ == 0 {
                        leanh::lean_ctor_set(v___x_3008_, 0, v___x_3011_);
                        v___x_3015_ = v___x_3008_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3016_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3011_);
                        v___x_3015_ = v_reuseFailAlloc_3016_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3003_);
                    if v_isShared_3009_ == 0 {
                        leanh::lean_ctor_set(v___x_3008_, 0, v___x_3011_);
                        v___x_3018_ = v___x_3008_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3019_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3011_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3019_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3006_,
                        );
                        v___x_3018_ = v_reuseFailAlloc_3019_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3015_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_o_3021_: *mut leanh::LeanObject,
    mut v_k_3022_: *mut leanh::LeanObject,
    mut v_v_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_3024_: u8 = 0;
    let mut v_res_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3024_ = (leanh::lean_unbox(v_v_3023_) as u8);
    v_res_3025_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_o_3021_, v_k_3022_, v_v_boxed_3024_);
    return v_res_3025_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(
    mut v_opts_3026_: *mut leanh::LeanObject,
    mut v_opt_3027_: *mut leanh::LeanObject,
    mut v_val_3028_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3029_ = leanh::lean_ctor_get(v_opt_3027_, 0);
    leanh::lean_inc(v_name_3029_);
    leanh::lean_dec_ref(v_opt_3027_);
    v___x_3030_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_opts_3026_, v_name_3029_, v_val_3028_);
    return v___x_3030_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(
    mut v_opts_3031_: *mut leanh::LeanObject,
    mut v_opt_3032_: *mut leanh::LeanObject,
    mut v_val_3033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_3034_: u8 = 0;
    let mut v_res_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_3034_ = (leanh::lean_unbox(v_val_3033_) as u8);
    v_res_3035_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_3031_, v_opt_3032_, v_val_boxed_3034_);
    return v_res_3035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(
    mut v_f_3036_: *mut leanh::LeanObject,
    mut v_keys_3037_: *mut leanh::LeanObject,
    mut v_vals_3038_: *mut leanh::LeanObject,
    mut v_i_3039_: *mut leanh::LeanObject,
    mut v_acc_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3041_ = lean_array_get_size(v_keys_3037_);
                v___x_3042_ = lean_nat_dec_lt(v_i_3039_, v___x_3041_);
                if v___x_3042_ == 0 {
                    leanh::lean_dec(v_i_3039_);
                    leanh::lean_dec_ref(v_f_3036_);
                    v___x_3043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3043_, 0, v_acc_3040_);
                    return v___x_3043_;
                } else {
                    v_k_3044_ = lean_array_fget_borrowed(v_keys_3037_, v_i_3039_);
                    v_v_3045_ = lean_array_fget_borrowed(v_vals_3038_, v_i_3039_);
                    leanh::lean_inc_ref(v_f_3036_);
                    leanh::lean_inc(v_v_3045_);
                    leanh::lean_inc(v_k_3044_);
                    v___x_3046_ =
                        leanh::lean_apply_3(v_f_3036_, v_acc_3040_, v_k_3044_, v_v_3045_);
                    if leanh::lean_obj_tag(v___x_3046_) == 0 {
                        leanh::lean_dec(v_i_3039_);
                        leanh::lean_dec_ref(v_f_3036_);
                        return v___x_3046_;
                    } else {
                        v_a_3047_ = leanh::lean_ctor_get(v___x_3046_, 0);
                        leanh::lean_inc(v_a_3047_);
                        leanh::lean_dec_ref_known(v___x_3046_, 1);
                        v___x_3048_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3049_ = lean_nat_add(v_i_3039_, v___x_3048_);
                        leanh::lean_dec(v_i_3039_);
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
    mut v_f_3051_: *mut leanh::LeanObject,
    mut v_keys_3052_: *mut leanh::LeanObject,
    mut v_vals_3053_: *mut leanh::LeanObject,
    mut v_i_3054_: *mut leanh::LeanObject,
    mut v_acc_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_3051_, v_keys_3052_, v_vals_3053_, v_i_3054_, v_acc_3055_);
    leanh::lean_dec_ref(v_vals_3053_);
    leanh::lean_dec_ref(v_keys_3052_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(
    mut v_f_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
    mut v_x_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: usize = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_ks_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3058_) == 0 {
                    v_es_3060_ = leanh::lean_ctor_get(v_x_3058_, 0);
                    v_isSharedCheck_3080_ = (!leanh::lean_is_exclusive(v_x_3058_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3062_ = v_x_3058_;
                        v_isShared_3063_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_3060_);
                        leanh::lean_dec(v_x_3058_);
                        v___x_3062_ = leanh::lean_box(0);
                        v_isShared_3063_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3081_ = leanh::lean_ctor_get(v_x_3058_, 0);
                    leanh::lean_inc_ref(v_ks_3081_);
                    v_vs_3082_ = leanh::lean_ctor_get(v_x_3058_, 1);
                    leanh::lean_inc_ref(v_vs_3082_);
                    leanh::lean_dec_ref_known(v_x_3058_, 2);
                    v___x_3083_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_3057_, v_ks_3081_, v_vs_3082_, v___x_3083_, v_x_3059_);
                    leanh::lean_dec_ref(v_vs_3082_);
                    leanh::lean_dec_ref(v_ks_3081_);
                    return v___x_3084_;
                }
            }
            1 => {
                v___x_3064_ = leanh::lean_unsigned_to_nat(0);
                v___x_3065_ = lean_array_get_size(v_es_3060_);
                v___x_3066_ = lean_nat_dec_lt(v___x_3064_, v___x_3065_);
                if v___x_3066_ == 0 {
                    leanh::lean_dec_ref(v_es_3060_);
                    leanh::lean_dec_ref(v_f_3057_);
                    if v_isShared_3063_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3062_, 1);
                        leanh::lean_ctor_set(v___x_3062_, 0, v_x_3059_);
                        v___x_3068_ = v___x_3062_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_x_3059_);
                        v___x_3068_ = v_reuseFailAlloc_3069_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3070_ = lean_nat_dec_le(v___x_3065_, v___x_3065_);
                    if v___x_3070_ == 0 {
                        if v___x_3066_ == 0 {
                            leanh::lean_dec_ref(v_es_3060_);
                            leanh::lean_dec_ref(v_f_3057_);
                            if v_isShared_3063_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3062_, 1);
                                leanh::lean_ctor_set(v___x_3062_, 0, v_x_3059_);
                                v___x_3072_ = v___x_3062_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3073_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_x_3059_);
                                v___x_3072_ = v_reuseFailAlloc_3073_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3062_);
                            v___x_3074_ = 0usize;
                            v___x_3075_ = lean_usize_of_nat(v___x_3065_);
                            v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3057_, v_es_3060_, v___x_3074_, v___x_3075_, v_x_3059_);
                            leanh::lean_dec_ref(v_es_3060_);
                            return v___x_3076_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3062_);
                        v___x_3077_ = 0usize;
                        v___x_3078_ = lean_usize_of_nat(v___x_3065_);
                        v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3057_, v_es_3060_, v___x_3077_, v___x_3078_, v_x_3059_);
                        leanh::lean_dec_ref(v_es_3060_);
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
    mut v_f_3085_: *mut leanh::LeanObject,
    mut v_as_3086_: *mut leanh::LeanObject,
    mut v_i_3087_: usize,
    mut v_stop_3088_: usize,
    mut v_b_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: usize = 0;
    let mut v___x_3093_: usize = 0;
    let mut v___y_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3098_ = lean_usize_dec_eq(v_i_3087_, v_stop_3088_);
                if v___x_3098_ == 0 {
                    v___x_3099_ = lean_array_uget_borrowed(v_as_3086_, v_i_3087_);
                    match leanh::lean_obj_tag(v___x_3099_) {
                        0 => {
                            v_key_3100_ = leanh::lean_ctor_get(v___x_3099_, 0);
                            v_val_3101_ = leanh::lean_ctor_get(v___x_3099_, 1);
                            leanh::lean_inc_ref(v_f_3085_);
                            leanh::lean_inc(v_val_3101_);
                            leanh::lean_inc(v_key_3100_);
                            v___x_3102_ = leanh::lean_apply_3(
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
                            v_node_3103_ = leanh::lean_ctor_get(v___x_3099_, 0);
                            leanh::lean_inc(v_node_3103_);
                            leanh::lean_inc_ref(v_f_3085_);
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
                    leanh::lean_dec_ref(v_f_3085_);
                    v___x_3105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3105_, 0, v_b_3089_);
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
                if leanh::lean_obj_tag(v___y_3096_) == 0 {
                    leanh::lean_dec_ref(v_f_3085_);
                    return v___y_3096_;
                } else {
                    v_a_3097_ = leanh::lean_ctor_get(v___y_3096_, 0);
                    leanh::lean_inc(v_a_3097_);
                    leanh::lean_dec_ref_known(v___y_3096_, 1);
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
    mut v_f_3106_: *mut leanh::LeanObject,
    mut v_as_3107_: *mut leanh::LeanObject,
    mut v_i_3108_: *mut leanh::LeanObject,
    mut v_stop_3109_: *mut leanh::LeanObject,
    mut v_b_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3111_: usize = 0;
    let mut v_stop_boxed_3112_: usize = 0;
    let mut v_res_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3111_ = leanh::lean_unbox_usize(v_i_3108_);
    leanh::lean_dec(v_i_3108_);
    v_stop_boxed_3112_ = leanh::lean_unbox_usize(v_stop_3109_);
    leanh::lean_dec(v_stop_3109_);
    v_res_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_3106_, v_as_3107_, v_i_boxed_3111_, v_stop_boxed_3112_, v_b_3110_);
    leanh::lean_dec_ref(v_as_3107_);
    return v_res_3113_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(
    mut v_f_3114_: *mut leanh::LeanObject,
    mut v_s_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
    mut v_b_3117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_a_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3118_, 0, v_a_3116_);
                leanh::lean_ctor_set(v___x_3118_, 1, v_b_3117_);
                v___x_3119_ = leanh::lean_apply_2(v_f_3114_, v___x_3118_, v_s_3115_);
                if leanh::lean_obj_tag(v___x_3119_) == 0 {
                    v_a_3120_ = leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3127_ = (!leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v___x_3122_ = v___x_3119_;
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3120_);
                        leanh::lean_dec(v___x_3119_);
                        v___x_3122_ = leanh::lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3128_);
                        leanh::lean_dec(v___x_3119_);
                        v___x_3130_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
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
                    v_reuseFailAlloc_3134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
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
    mut v_map_3136_: *mut leanh::LeanObject,
    mut v_init_3137_: *mut leanh::LeanObject,
    mut v_f_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3139_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_3139_, 0, v_f_3138_);
    leanh::lean_inc_ref(v_map_3136_);
    v___x_3140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v___f_3139_, v_map_3136_, v_init_3137_);
    v_a_3141_ = leanh::lean_ctor_get(v___x_3140_, 0);
    leanh::lean_inc(v_a_3141_);
    leanh::lean_dec_ref(v___x_3140_);
    return v_a_3141_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(
    mut v_map_3142_: *mut leanh::LeanObject,
    mut v_init_3143_: *mut leanh::LeanObject,
    mut v_f_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_3142_, v_init_3143_, v_f_3144_);
    leanh::lean_dec_ref(v_map_3142_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(
    mut v_x_3146_: *mut leanh::LeanObject,
    mut v_x_3147_: *mut leanh::LeanObject,
    mut v_x_3148_: *mut leanh::LeanObject,
    mut v_x_3149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3150_ = leanh::lean_ctor_get(v_x_3146_, 0);
                v_vs_3151_ = leanh::lean_ctor_get(v_x_3146_, 1);
                v_isSharedCheck_3175_ = (!leanh::lean_is_exclusive(v_x_3146_)) as u8;
                if v_isSharedCheck_3175_ == 0 {
                    v___x_3153_ = v_x_3146_;
                    v_isShared_3154_ = v_isSharedCheck_3175_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3151_);
                    leanh::lean_inc(v_ks_3150_);
                    leanh::lean_dec(v_x_3146_);
                    v___x_3153_ = leanh::lean_box(0);
                    v_isShared_3154_ = v_isSharedCheck_3175_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3155_ = lean_array_get_size(v_ks_3150_);
                v___x_3156_ = lean_nat_dec_lt(v_x_3147_, v___x_3155_);
                if v___x_3156_ == 0 {
                    leanh::lean_dec(v_x_3147_);
                    v___x_3157_ = lean_array_push(v_ks_3150_, v_x_3148_);
                    v___x_3158_ = lean_array_push(v_vs_3151_, v_x_3149_);
                    if v_isShared_3154_ == 0 {
                        leanh::lean_ctor_set(v___x_3153_, 1, v___x_3158_);
                        leanh::lean_ctor_set(v___x_3153_, 0, v___x_3157_);
                        v___x_3160_ = v___x_3153_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3161_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___x_3158_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_ks_3150_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_vs_3151_);
                            v___x_3165_ = v_reuseFailAlloc_3169_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3170_ = lean_array_fset(v_ks_3150_, v_x_3147_, v_x_3148_);
                        v___x_3171_ = lean_array_fset(v_vs_3151_, v_x_3147_, v_x_3149_);
                        leanh::lean_dec(v_x_3147_);
                        if v_isShared_3154_ == 0 {
                            leanh::lean_ctor_set(v___x_3153_, 1, v___x_3171_);
                            leanh::lean_ctor_set(v___x_3153_, 0, v___x_3170_);
                            v___x_3173_ = v___x_3153_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3174_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3170_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3171_);
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
                v___x_3166_ = leanh::lean_unsigned_to_nat(1);
                v___x_3167_ = lean_nat_add(v_x_3147_, v___x_3166_);
                leanh::lean_dec(v_x_3147_);
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
    mut v_n_3176_: *mut leanh::LeanObject,
    mut v_k_3177_: *mut leanh::LeanObject,
    mut v_v_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = leanh::lean_unsigned_to_nat(0);
    v___x_3180_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_n_3176_, v___x_3179_, v_k_3177_, v_v_3178_);
    return v___x_3180_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0()
-> u64 {
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u64 = 0;
    v___x_3181_ = leanh::lean_unsigned_to_nat(1723);
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
    v___x_3187_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0);
    v___x_3188_ = lean_usize_sub(v___x_3187_, v___x_3186_);
    return v___x_3188_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3189_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(
    mut v_x_3190_: *mut leanh::LeanObject,
    mut v_x_3191_: usize,
    mut v_x_3192_: usize,
    mut v_x_3193_: *mut leanh::LeanObject,
    mut v_x_3194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v_j_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v_v_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v_node_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_unused_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: u8 = 0;
    let mut v_ks_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: usize = 0;
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v_reuseFailAlloc_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3190_) == 0 {
                    v_es_3195_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v___x_3196_ = 5usize;
                    v___x_3197_ = 1usize;
                    v___x_3198_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
                    v___x_3199_ = lean_usize_land(v_x_3191_, v___x_3198_);
                    v_j_3200_ = lean_usize_to_nat(v___x_3199_);
                    v___x_3201_ = lean_array_get_size(v_es_3195_);
                    v___x_3202_ = lean_nat_dec_lt(v_j_3200_, v___x_3201_);
                    if v___x_3202_ == 0 {
                        leanh::lean_dec(v_j_3200_);
                        leanh::lean_dec(v_x_3194_);
                        leanh::lean_dec(v_x_3193_);
                        return v_x_3190_;
                    } else {
                        leanh::lean_inc_ref(v_es_3195_);
                        v_isSharedCheck_3239_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                        if v_isSharedCheck_3239_ == 0 {
                            v_unused_3240_ = leanh::lean_ctor_get(v_x_3190_, 0);
                            leanh::lean_dec(v_unused_3240_);
                            v___x_3204_ = v_x_3190_;
                            v_isShared_3205_ = v_isSharedCheck_3239_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3190_);
                            v___x_3204_ = leanh::lean_box(0);
                            v_isShared_3205_ = v_isSharedCheck_3239_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3241_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_vs_3242_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3262_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3244_ = v_x_3190_;
                        v_isShared_3245_ = v_isSharedCheck_3262_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3242_);
                        leanh::lean_inc(v_ks_3241_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3244_ = leanh::lean_box(0);
                        v_isShared_3245_ = v_isSharedCheck_3262_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3206_ = lean_array_fget(v_es_3195_, v_j_3200_);
                v___x_3207_ = leanh::lean_box(0);
                v_xs_x27_3208_ = lean_array_fset(v_es_3195_, v_j_3200_, v___x_3207_);
                match leanh::lean_obj_tag(v_v_3206_) {
                    0 => {
                        v_key_3215_ = leanh::lean_ctor_get(v_v_3206_, 0);
                        v_val_3216_ = leanh::lean_ctor_get(v_v_3206_, 1);
                        v_isSharedCheck_3226_ = (!leanh::lean_is_exclusive(v_v_3206_)) as u8;
                        if v_isSharedCheck_3226_ == 0 {
                            v___x_3218_ = v_v_3206_;
                            v_isShared_3219_ = v_isSharedCheck_3226_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3216_);
                            leanh::lean_inc(v_key_3215_);
                            leanh::lean_dec(v_v_3206_);
                            v___x_3218_ = leanh::lean_box(0);
                            v_isShared_3219_ = v_isSharedCheck_3226_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3227_ = leanh::lean_ctor_get(v_v_3206_, 0);
                        v_isSharedCheck_3237_ = (!leanh::lean_is_exclusive(v_v_3206_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3229_ = v_v_3206_;
                            v_isShared_3230_ = v_isSharedCheck_3237_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3227_);
                            leanh::lean_dec(v_v_3206_);
                            v___x_3229_ = leanh::lean_box(0);
                            v_isShared_3230_ = v_isSharedCheck_3237_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3238_, 0, v_x_3193_);
                        leanh::lean_ctor_set(v___x_3238_, 1, v_x_3194_);
                        v___y_3210_ = v___x_3238_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3211_ = lean_array_fset(v_xs_x27_3208_, v_j_3200_, v___y_3210_);
                leanh::lean_dec(v_j_3200_);
                if v_isShared_3205_ == 0 {
                    leanh::lean_ctor_set(v___x_3204_, 0, v___x_3211_);
                    v___x_3213_ = v___x_3204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
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
                    leanh::lean_del_object(v___x_3218_);
                    v___x_3221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3215_,
                        v_val_3216_,
                        v_x_3193_,
                        v_x_3194_,
                    );
                    v___x_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3222_, 0, v___x_3221_);
                    v___y_3210_ = v___x_3222_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3216_);
                    leanh::lean_dec(v_key_3215_);
                    if v_isShared_3219_ == 0 {
                        leanh::lean_ctor_set(v___x_3218_, 1, v_x_3194_);
                        leanh::lean_ctor_set(v___x_3218_, 0, v_x_3193_);
                        v___x_3224_ = v___x_3218_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_x_3193_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_x_3194_);
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
                    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3233_);
                    v___x_3235_ = v___x_3229_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
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
                    v_reuseFailAlloc_3261_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_ks_3241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_vs_3242_);
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
                    v___x_3259_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3260_ = lean_nat_dec_lt(v___x_3258_, v___x_3259_);
                    leanh::lean_dec(v___x_3258_);
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
                    v_ks_3251_ = leanh::lean_ctor_get(v_newNode_3248_, 0);
                    leanh::lean_inc_ref(v_ks_3251_);
                    v_vs_3252_ = leanh::lean_ctor_get(v_newNode_3248_, 1);
                    leanh::lean_inc_ref(v_vs_3252_);
                    leanh::lean_dec_ref(v_newNode_3248_);
                    v___x_3253_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2);
                    v___x_3255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_x_3192_, v_ks_3251_, v_vs_3252_, v___x_3253_, v___x_3254_);
                    leanh::lean_dec_ref(v_vs_3252_);
                    leanh::lean_dec_ref(v_ks_3251_);
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
    mut v_keys_3264_: *mut leanh::LeanObject,
    mut v_vals_3265_: *mut leanh::LeanObject,
    mut v_i_3266_: *mut leanh::LeanObject,
    mut v_entries_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v_k_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3273_: u64 = 0;
    let mut v_h_3274_: usize = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v_h_3280_: usize = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u64 = 0;
    let mut v_hash_3285_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3268_ = lean_array_get_size(v_keys_3264_);
                v___x_3269_ = lean_nat_dec_lt(v_i_3266_, v___x_3268_);
                if v___x_3269_ == 0 {
                    leanh::lean_dec(v_i_3266_);
                    return v_entries_3267_;
                } else {
                    v_k_3270_ = lean_array_fget_borrowed(v_keys_3264_, v_i_3266_);
                    v_v_3271_ = lean_array_fget_borrowed(v_vals_3265_, v_i_3266_);
                    if leanh::lean_obj_tag(v_k_3270_) == 0 {
                        v___x_3284_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                        v___y_3273_ = v___x_3284_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3285_ = leanh::lean_ctor_get_uint64(
                            v_k_3270_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                v___x_3276_ = leanh::lean_unsigned_to_nat(1);
                v___x_3277_ = 1usize;
                v___x_3278_ = lean_usize_sub(v_depth_3263_, v___x_3277_);
                v___x_3279_ = lean_usize_mul(v___x_3275_, v___x_3278_);
                v_h_3280_ = lean_usize_shift_right(v_h_3274_, v___x_3279_);
                v___x_3281_ = lean_nat_add(v_i_3266_, v___x_3276_);
                leanh::lean_dec(v_i_3266_);
                leanh::lean_inc(v_v_3271_);
                leanh::lean_inc(v_k_3270_);
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
    mut v_depth_3286_: *mut leanh::LeanObject,
    mut v_keys_3287_: *mut leanh::LeanObject,
    mut v_vals_3288_: *mut leanh::LeanObject,
    mut v_i_3289_: *mut leanh::LeanObject,
    mut v_entries_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3291_: usize = 0;
    let mut v_res_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3291_ = leanh::lean_unbox_usize(v_depth_3286_);
    leanh::lean_dec(v_depth_3286_);
    v_res_3292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_boxed_3291_, v_keys_3287_, v_vals_3288_, v_i_3289_, v_entries_3290_);
    leanh::lean_dec_ref(v_vals_3288_);
    leanh::lean_dec_ref(v_keys_3287_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___boxed(
    mut v_x_3293_: *mut leanh::LeanObject,
    mut v_x_3294_: *mut leanh::LeanObject,
    mut v_x_3295_: *mut leanh::LeanObject,
    mut v_x_3296_: *mut leanh::LeanObject,
    mut v_x_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30371__boxed_3298_: usize = 0;
    let mut v_x_30372__boxed_3299_: usize = 0;
    let mut v_res_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30371__boxed_3298_ = leanh::lean_unbox_usize(v_x_3294_);
    leanh::lean_dec(v_x_3294_);
    v_x_30372__boxed_3299_ = leanh::lean_unbox_usize(v_x_3295_);
    leanh::lean_dec(v_x_3295_);
    v_res_3300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_3293_, v_x_30371__boxed_3298_, v_x_30372__boxed_3299_, v_x_3296_, v_x_3297_);
    return v_res_3300_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(
    mut v_x_3301_: *mut leanh::LeanObject,
    mut v_x_3302_: *mut leanh::LeanObject,
    mut v_x_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3305_: u64 = 0;
    let mut v___x_3306_: usize = 0;
    let mut v___x_3307_: usize = 0;
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u64 = 0;
    let mut v_hash_3310_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3302_) == 0 {
                    v___x_3309_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                    v___y_3305_ = v___x_3309_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3310_ = leanh::lean_ctor_get_uint64(
                        v_x_3302_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_keys_3311_: *mut leanh::LeanObject,
    mut v_vals_3312_: *mut leanh::LeanObject,
    mut v_i_3313_: *mut leanh::LeanObject,
    mut v_k_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3315_ = lean_array_get_size(v_keys_3311_);
                v___x_3316_ = lean_nat_dec_lt(v_i_3313_, v___x_3315_);
                if v___x_3316_ == 0 {
                    leanh::lean_dec(v_i_3313_);
                    v___x_3317_ = leanh::lean_box(0);
                    return v___x_3317_;
                } else {
                    v_k_x27_3318_ = lean_array_fget_borrowed(v_keys_3311_, v_i_3313_);
                    v___x_3319_ = lean_name_eq(v_k_3314_, v_k_x27_3318_);
                    if v___x_3319_ == 0 {
                        v___x_3320_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3321_ = lean_nat_add(v_i_3313_, v___x_3320_);
                        leanh::lean_dec(v_i_3313_);
                        v_i_3313_ = v___x_3321_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3323_ = lean_array_fget_borrowed(v_vals_3312_, v_i_3313_);
                        leanh::lean_dec(v_i_3313_);
                        leanh::lean_inc(v___x_3323_);
                        v___x_3324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3324_, 0, v___x_3323_);
                        return v___x_3324_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg___boxed(
    mut v_keys_3325_: *mut leanh::LeanObject,
    mut v_vals_3326_: *mut leanh::LeanObject,
    mut v_i_3327_: *mut leanh::LeanObject,
    mut v_k_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_3325_, v_vals_3326_, v_i_3327_, v_k_3328_);
    leanh::lean_dec(v_k_3328_);
    leanh::lean_dec_ref(v_vals_3326_);
    leanh::lean_dec_ref(v_keys_3325_);
    return v_res_3329_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(
    mut v_x_3330_: *mut leanh::LeanObject,
    mut v_x_3331_: usize,
    mut v_x_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: usize = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: usize = 0;
    let mut v_j_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: usize = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3330_) == 0 {
                    v_es_3333_ = leanh::lean_ctor_get(v_x_3330_, 0);
                    v___x_3334_ = leanh::lean_box(2);
                    v___x_3335_ = 5usize;
                    v___x_3336_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
                    v___x_3337_ = lean_usize_land(v_x_3331_, v___x_3336_);
                    v_j_3338_ = lean_usize_to_nat(v___x_3337_);
                    v___x_3339_ = lean_array_get_borrowed(v___x_3334_, v_es_3333_, v_j_3338_);
                    leanh::lean_dec(v_j_3338_);
                    match leanh::lean_obj_tag(v___x_3339_) {
                        0 => {
                            v_key_3340_ = leanh::lean_ctor_get(v___x_3339_, 0);
                            v_val_3341_ = leanh::lean_ctor_get(v___x_3339_, 1);
                            v___x_3342_ = lean_name_eq(v_x_3332_, v_key_3340_);
                            if v___x_3342_ == 0 {
                                v___x_3343_ = leanh::lean_box(0);
                                return v___x_3343_;
                            } else {
                                leanh::lean_inc(v_val_3341_);
                                v___x_3344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3344_, 0, v_val_3341_);
                                return v___x_3344_;
                            }
                        }
                        1 => {
                            v_node_3345_ = leanh::lean_ctor_get(v___x_3339_, 0);
                            v___x_3346_ = lean_usize_shift_right(v_x_3331_, v___x_3335_);
                            v_x_3330_ = v_node_3345_;
                            v_x_3331_ = v___x_3346_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3348_ = leanh::lean_box(0);
                            return v___x_3348_;
                        }
                    }
                } else {
                    v_ks_3349_ = leanh::lean_ctor_get(v_x_3330_, 0);
                    v_vs_3350_ = leanh::lean_ctor_get(v_x_3330_, 1);
                    v___x_3351_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3352_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_ks_3349_, v_vs_3350_, v___x_3351_, v_x_3332_);
                    return v___x_3352_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg___boxed(
    mut v_x_3353_: *mut leanh::LeanObject,
    mut v_x_3354_: *mut leanh::LeanObject,
    mut v_x_3355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30582__boxed_3356_: usize = 0;
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30582__boxed_3356_ = leanh::lean_unbox_usize(v_x_3354_);
    leanh::lean_dec(v_x_3354_);
    v_res_3357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_3353_, v_x_30582__boxed_3356_, v_x_3355_);
    leanh::lean_dec(v_x_3355_);
    leanh::lean_dec_ref(v_x_3353_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(
    mut v_x_3358_: *mut leanh::LeanObject,
    mut v_x_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3361_: u64 = 0;
    let mut v___x_3362_: usize = 0;
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u64 = 0;
    let mut v_hash_3365_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3359_) == 0 {
                    v___x_3364_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
                    v___y_3361_ = v___x_3364_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3365_ = leanh::lean_ctor_get_uint64(
                        v_x_3359_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_3366_: *mut leanh::LeanObject,
    mut v_x_3367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_3366_, v_x_3367_);
    leanh::lean_dec(v_x_3367_);
    leanh::lean_dec_ref(v_x_3366_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(
    mut v_oldCounters_3369_: *mut leanh::LeanObject,
    mut v_x_3370_: *mut leanh::LeanObject,
    mut v_____s_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_result_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3372_ = leanh::lean_ctor_get(v_x_3370_, 0);
                leanh::lean_inc(v_fst_3372_);
                v_snd_3373_ = leanh::lean_ctor_get(v_x_3370_, 1);
                leanh::lean_inc(v_snd_3373_);
                leanh::lean_dec_ref(v_x_3370_);
                v___x_3374_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_oldCounters_3369_, v_fst_3372_);
                if leanh::lean_obj_tag(v___x_3374_) == 1 {
                    v_val_3375_ = leanh::lean_ctor_get(v___x_3374_, 0);
                    v_isSharedCheck_3384_ = (!leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3384_ == 0 {
                        v___x_3377_ = v___x_3374_;
                        v_isShared_3378_ = v_isSharedCheck_3384_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3375_);
                        leanh::lean_dec(v___x_3374_);
                        v___x_3377_ = leanh::lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3384_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3374_);
                    v_result_3385_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_3371_, v_fst_3372_, v_snd_3373_);
                    v___x_3386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3386_, 0, v_result_3385_);
                    return v___x_3386_;
                }
            }
            1 => {
                v___x_3379_ = lean_nat_sub(v_snd_3373_, v_val_3375_);
                leanh::lean_dec(v_val_3375_);
                leanh::lean_dec(v_snd_3373_);
                v_result_3380_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_3371_, v_fst_3372_, v___x_3379_);
                if v_isShared_3378_ == 0 {
                    leanh::lean_ctor_set(v___x_3377_, 0, v_result_3380_);
                    v___x_3382_ = v___x_3377_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_result_3380_);
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
    mut v_oldCounters_3387_: *mut leanh::LeanObject,
    mut v_x_3388_: *mut leanh::LeanObject,
    mut v_____s_3389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3390_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(v_oldCounters_3387_, v_x_3388_, v_____s_3389_);
    leanh::lean_dec_ref(v_oldCounters_3387_);
    return v_res_3390_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3391_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once), _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0);
    v_result_3393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v_result_3393_, 0, v___x_3392_);
    return v_result_3393_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(
    mut v_newCounters_3394_: *mut leanh::LeanObject,
    mut v_oldCounters_3395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3396_ = leanh::lean_alloc_closure(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_3396_, 0, v_oldCounters_3395_);
    v_result_3397_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once), _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1);
    v___x_3398_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_newCounters_3394_, v_result_3397_, v___f_3396_);
    return v___x_3398_;
}
pub unsafe fn l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___boxed(
    mut v_newCounters_3399_: *mut leanh::LeanObject,
    mut v_oldCounters_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_newCounters_3399_, v_oldCounters_3400_);
    leanh::lean_dec_ref(v_newCounters_3399_);
    return v_res_3401_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(
    mut v_f_3402_: *mut leanh::LeanObject,
    mut v_keys_3403_: *mut leanh::LeanObject,
    mut v_vals_3404_: *mut leanh::LeanObject,
    mut v_i_3405_: *mut leanh::LeanObject,
    mut v_acc_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    let mut v_k_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3407_ = lean_array_get_size(v_keys_3403_);
                v___x_3408_ = lean_nat_dec_lt(v_i_3405_, v___x_3407_);
                if v___x_3408_ == 0 {
                    leanh::lean_dec(v_i_3405_);
                    leanh::lean_dec(v_f_3402_);
                    return v_acc_3406_;
                } else {
                    v_k_3409_ = lean_array_fget_borrowed(v_keys_3403_, v_i_3405_);
                    v_v_3410_ = lean_array_fget_borrowed(v_vals_3404_, v_i_3405_);
                    leanh::lean_inc(v_f_3402_);
                    leanh::lean_inc(v_v_3410_);
                    leanh::lean_inc(v_k_3409_);
                    v___x_3411_ =
                        leanh::lean_apply_3(v_f_3402_, v_acc_3406_, v_k_3409_, v_v_3410_);
                    v___x_3412_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3413_ = lean_nat_add(v_i_3405_, v___x_3412_);
                    leanh::lean_dec(v_i_3405_);
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
    mut v_f_3415_: *mut leanh::LeanObject,
    mut v_keys_3416_: *mut leanh::LeanObject,
    mut v_vals_3417_: *mut leanh::LeanObject,
    mut v_i_3418_: *mut leanh::LeanObject,
    mut v_acc_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_3415_, v_keys_3416_, v_vals_3417_, v_i_3418_, v_acc_3419_);
    leanh::lean_dec_ref(v_vals_3417_);
    leanh::lean_dec_ref(v_keys_3416_);
    return v_res_3420_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(
    mut v_f_3421_: *mut leanh::LeanObject,
    mut v_x_3422_: *mut leanh::LeanObject,
    mut v_x_3423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3422_) == 0 {
        let mut v_es_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3427_: u8 = 0;
        v_es_3424_ = leanh::lean_ctor_get(v_x_3422_, 0);
        v___x_3425_ = leanh::lean_unsigned_to_nat(0);
        v___x_3426_ = lean_array_get_size(v_es_3424_);
        v___x_3427_ = lean_nat_dec_lt(v___x_3425_, v___x_3426_);
        if v___x_3427_ == 0 {
            leanh::lean_dec(v_f_3421_);
            return v_x_3423_;
        } else {
            let mut v___x_3428_: u8 = 0;
            v___x_3428_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
            if v___x_3428_ == 0 {
                if v___x_3427_ == 0 {
                    leanh::lean_dec(v_f_3421_);
                    return v_x_3423_;
                } else {
                    let mut v___x_3429_: usize = 0;
                    let mut v___x_3430_: usize = 0;
                    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3429_ = 0usize;
                    v___x_3430_ = lean_usize_of_nat(v___x_3426_);
                    v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3421_, v_es_3424_, v___x_3429_, v___x_3430_, v_x_3423_);
                    return v___x_3431_;
                }
            } else {
                let mut v___x_3432_: usize = 0;
                let mut v___x_3433_: usize = 0;
                let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3432_ = 0usize;
                v___x_3433_ = lean_usize_of_nat(v___x_3426_);
                v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3421_, v_es_3424_, v___x_3432_, v___x_3433_, v_x_3423_);
                return v___x_3434_;
            }
        }
    } else {
        let mut v_ks_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_3435_ = leanh::lean_ctor_get(v_x_3422_, 0);
        v_vs_3436_ = leanh::lean_ctor_get(v_x_3422_, 1);
        v___x_3437_ = leanh::lean_unsigned_to_nat(0);
        v___x_3438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_3421_, v_ks_3435_, v_vs_3436_, v___x_3437_, v_x_3423_);
        return v___x_3438_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(
    mut v_f_3439_: *mut leanh::LeanObject,
    mut v_as_3440_: *mut leanh::LeanObject,
    mut v_i_3441_: usize,
    mut v_stop_3442_: usize,
    mut v_b_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3449_ = lean_usize_dec_eq(v_i_3441_, v_stop_3442_);
                if v___x_3449_ == 0 {
                    v___x_3450_ = lean_array_uget_borrowed(v_as_3440_, v_i_3441_);
                    match leanh::lean_obj_tag(v___x_3450_) {
                        0 => {
                            v_key_3451_ = leanh::lean_ctor_get(v___x_3450_, 0);
                            v_val_3452_ = leanh::lean_ctor_get(v___x_3450_, 1);
                            leanh::lean_inc(v_f_3439_);
                            leanh::lean_inc(v_val_3452_);
                            leanh::lean_inc(v_key_3451_);
                            v___x_3453_ = leanh::lean_apply_3(
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
                            v_node_3454_ = leanh::lean_ctor_get(v___x_3450_, 0);
                            leanh::lean_inc(v_f_3439_);
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
                    leanh::lean_dec(v_f_3439_);
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
    mut v_f_3456_: *mut leanh::LeanObject,
    mut v_as_3457_: *mut leanh::LeanObject,
    mut v_i_3458_: *mut leanh::LeanObject,
    mut v_stop_3459_: *mut leanh::LeanObject,
    mut v_b_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3461_: usize = 0;
    let mut v_stop_boxed_3462_: usize = 0;
    let mut v_res_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3461_ = leanh::lean_unbox_usize(v_i_3458_);
    leanh::lean_dec(v_i_3458_);
    v_stop_boxed_3462_ = leanh::lean_unbox_usize(v_stop_3459_);
    leanh::lean_dec(v_stop_3459_);
    v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_3456_, v_as_3457_, v_i_boxed_3461_, v_stop_boxed_3462_, v_b_3460_);
    leanh::lean_dec_ref(v_as_3457_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg___boxed(
    mut v_f_3464_: *mut leanh::LeanObject,
    mut v_x_3465_: *mut leanh::LeanObject,
    mut v_x_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_3464_, v_x_3465_, v_x_3466_);
    leanh::lean_dec_ref(v_x_3465_);
    return v_res_3467_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0(
    mut v_f_3468_: *mut leanh::LeanObject,
    mut v_x1_3469_: *mut leanh::LeanObject,
    mut v_x2_3470_: *mut leanh::LeanObject,
    mut v_x3_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = leanh::lean_apply_3(v_f_3468_, v_x1_3469_, v_x2_3470_, v_x3_3471_);
    return v___x_3472_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(
    mut v_map_3473_: *mut leanh::LeanObject,
    mut v_f_3474_: *mut leanh::LeanObject,
    mut v_init_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3476_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_3476_, 0, v_f_3474_);
    v___x_3477_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v___f_3476_, v_map_3473_, v_init_3475_);
    return v___x_3477_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___boxed(
    mut v_map_3478_: *mut leanh::LeanObject,
    mut v_f_3479_: *mut leanh::LeanObject,
    mut v_init_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_3478_, v_f_3479_, v_init_3480_);
    leanh::lean_dec_ref(v_map_3478_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0(
    mut v_ps_3482_: *mut leanh::LeanObject,
    mut v_k_3483_: *mut leanh::LeanObject,
    mut v_v_3484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3485_, 0, v_k_3483_);
    leanh::lean_ctor_set(v___x_3485_, 1, v_v_3484_);
    v___x_3486_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3486_, 0, v___x_3485_);
    leanh::lean_ctor_set(v___x_3486_, 1, v_ps_3482_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(
    mut v_m_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3489_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0;
    v___x_3490_ = leanh::lean_box(0);
    v___x_3491_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_m_3488_, v___f_3489_, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___boxed(
    mut v_m_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_3492_);
    leanh::lean_dec_ref(v_m_3492_);
    return v_res_3493_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0;
    v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
    return v___x_3496_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2;
    v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
    return v___x_3499_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3500_ = leanh::lean_box(1);
    v___x_3501_ = l_Lean_MessageData_ofFormat(v___x_3500_);
    return v___x_3501_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3503_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5;
    v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
    return v___x_3504_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3508_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8;
    v___x_3509_ = l_Lean_MessageData_ofFormat(v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11;
    v___x_3514_ = l_Lean_MessageData_ofFormat(v___x_3513_);
    return v___x_3514_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3515_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13);
    v___x_3517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3517_, 0, v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14);
    v___x_3519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3519_, 0, v___x_3518_);
    leanh::lean_ctor_set(v___x_3519_, 1, v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(
    mut v_a_3520_: u8,
    mut v_kind_3521_: *mut leanh::LeanObject,
    mut v___x_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v___x_3524_: u8,
    mut v_diag_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
    mut v___y_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: u8 = 0;
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3593_: u8 = 0;
    let mut v_inheritedTraceOptions_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v_fileName_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3611_: u8 = 0;
    let mut v_inheritedTraceOptions_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_unused_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: u8 = 0;
    let mut v_reuseFailAlloc_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v_unused_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: u8 = 0;
    let mut v___y_3653_: u8 = 0;
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_unused_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3580_ = lean_st_ref_get(v___y_3529_);
                v_fileName_3581_ = leanh::lean_ctor_get(v___y_3528_, 0);
                v_fileMap_3582_ = leanh::lean_ctor_get(v___y_3528_, 1);
                v_options_3583_ = leanh::lean_ctor_get(v___y_3528_, 2);
                v_currRecDepth_3584_ = leanh::lean_ctor_get(v___y_3528_, 3);
                v_ref_3585_ = leanh::lean_ctor_get(v___y_3528_, 5);
                v_currNamespace_3586_ = leanh::lean_ctor_get(v___y_3528_, 6);
                v_openDecls_3587_ = leanh::lean_ctor_get(v___y_3528_, 7);
                v_initHeartbeats_3588_ = leanh::lean_ctor_get(v___y_3528_, 8);
                v_maxHeartbeats_3589_ = leanh::lean_ctor_get(v___y_3528_, 9);
                v_quotContext_3590_ = leanh::lean_ctor_get(v___y_3528_, 10);
                v_currMacroScope_3591_ = leanh::lean_ctor_get(v___y_3528_, 11);
                v_cancelTk_x3f_3592_ = leanh::lean_ctor_get(v___y_3528_, 12);
                v_suppressElabErrors_3593_ = leanh::lean_ctor_get_uint8(
                    v___y_3528_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3594_ = leanh::lean_ctor_get(v___y_3528_, 13);
                v_env_3595_ = leanh::lean_ctor_get(v___x_3580_, 0);
                leanh::lean_inc_ref(v_env_3595_);
                leanh::lean_dec(v___x_3580_);
                v___x_3596_ = l_Lean_diagnostics;
                leanh::lean_inc_ref(v_options_3583_);
                v___x_3597_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_options_3583_, v___x_3596_, v_a_3520_);
                v___x_3598_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___x_3597_, v___x_3596_);
                v___x_3674_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3595_);
                leanh::lean_dec_ref(v_env_3595_);
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
                    leanh::lean_dec_ref(v___y_3532_);
                    v___x_3534_ = leanh::lean_box(0);
                    v___x_3535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3535_, 0, v___x_3534_);
                    return v___x_3535_;
                } else {
                    v___x_3536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3536_, 0, v___y_3532_);
                    return v___x_3536_;
                }
            }
            2 => {
                v___x_3541_ = l_Lean_stringToMessageData(v_kind_3521_);
                v___x_3542_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1);
                v___x_3543_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3543_, 0, v___x_3541_);
                leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                leanh::lean_inc_ref(v___y_3540_);
                v___x_3544_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                leanh::lean_ctor_set(v___x_3544_, 1, v___y_3540_);
                v___x_3545_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3);
                v___x_3546_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3546_, 0, v___x_3544_);
                leanh::lean_ctor_set(v___x_3546_, 1, v___x_3545_);
                v___x_3547_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4);
                v___x_3548_ = l_Lean_MessageData_joinSep(v___y_3539_, v___x_3547_);
                v___x_3549_ = l_Lean_indentD(v___x_3548_);
                v___x_3550_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3550_, 0, v___x_3546_);
                leanh::lean_ctor_set(v___x_3550_, 1, v___x_3549_);
                v___x_3551_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6);
                v___x_3552_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3552_, 0, v___x_3550_);
                leanh::lean_ctor_set(v___x_3552_, 1, v___x_3551_);
                v___x_3553_ = l_Lean_Exception_toMessageData(v___y_3538_);
                v___x_3554_ = l_Lean_indentD(v___x_3553_);
                v___x_3555_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3555_, 0, v___x_3552_);
                leanh::lean_ctor_set(v___x_3555_, 1, v___x_3554_);
                v___x_3556_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3556_, 0, v___x_3555_);
                v___x_3557_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3557_, 0, v___x_3556_);
                return v___x_3557_;
            }
            3 => {
                if v___y_3562_ == 0 {
                    v___x_3563_ = lean_st_ref_get(v___y_3527_);
                    v___x_3564_ = lean_st_ref_get(v___y_3561_);
                    v_diag_3565_ = leanh::lean_ctor_get(v___x_3563_, 4);
                    leanh::lean_inc_ref(v_diag_3565_);
                    leanh::lean_dec(v___x_3563_);
                    v_unfoldCounter_3566_ = leanh::lean_ctor_get(v_diag_3565_, 0);
                    leanh::lean_inc_ref(v_unfoldCounter_3566_);
                    leanh::lean_dec_ref(v_diag_3565_);
                    v_env_3567_ = leanh::lean_ctor_get(v___x_3564_, 0);
                    leanh::lean_inc_ref(v_env_3567_);
                    leanh::lean_dec(v___x_3564_);
                    v___x_3568_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v___y_3560_, v_unfoldCounter_3566_);
                    leanh::lean_dec_ref(v___y_3560_);
                    v___x_3569_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v___x_3568_);
                    leanh::lean_dec_ref(v___x_3568_);
                    v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_3522_);
                    v___x_3571_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_env_3567_, v___x_3569_, v___x_3570_);
                    v___x_3572_ = l_List_isEmpty___redArg(v___x_3571_);
                    if v___x_3572_ == 0 {
                        v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3;
                        v___x_3574_ = lean_string_dec_eq(v_kind_3521_, v___x_3573_);
                        if v___x_3574_ == 0 {
                            v___x_3575_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9);
                            v___y_3538_ = v___y_3559_;
                            v___y_3539_ = v___x_3571_;
                            v___y_3540_ = v___x_3575_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12);
                            v___y_3538_ = v___y_3559_;
                            v___y_3539_ = v___x_3571_;
                            v___y_3540_ = v___x_3576_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3571_);
                        leanh::lean_dec_ref(v___y_3559_);
                        leanh::lean_dec_ref(v_kind_3521_);
                        v___x_3577_ = leanh::lean_box(0);
                        v___x_3578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3578_, 0, v___x_3577_);
                        return v___x_3578_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3560_);
                    leanh::lean_dec_ref(v_kind_3521_);
                    v___x_3579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3579_, 0, v___y_3559_);
                    return v___x_3579_;
                }
            }
            4 => {
                v___x_3614_ = l_Lean_maxRecDepth;
                v___x_3615_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v___x_3597_, v___x_3614_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_3612_);
                leanh::lean_inc(v_cancelTk_x3f_3610_);
                leanh::lean_inc(v_currMacroScope_3609_);
                leanh::lean_inc(v_quotContext_3608_);
                leanh::lean_inc(v_maxHeartbeats_3607_);
                leanh::lean_inc(v_initHeartbeats_3606_);
                leanh::lean_inc(v_openDecls_3605_);
                leanh::lean_inc(v_currNamespace_3604_);
                leanh::lean_inc(v_ref_3603_);
                leanh::lean_inc(v_currRecDepth_3602_);
                leanh::lean_inc_ref(v_fileMap_3601_);
                leanh::lean_inc_ref(v_fileName_3600_);
                v___x_3616_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_3616_, 0, v_fileName_3600_);
                leanh::lean_ctor_set(v___x_3616_, 1, v_fileMap_3601_);
                leanh::lean_ctor_set(v___x_3616_, 2, v___x_3597_);
                leanh::lean_ctor_set(v___x_3616_, 3, v_currRecDepth_3602_);
                leanh::lean_ctor_set(v___x_3616_, 4, v___x_3615_);
                leanh::lean_ctor_set(v___x_3616_, 5, v_ref_3603_);
                leanh::lean_ctor_set(v___x_3616_, 6, v_currNamespace_3604_);
                leanh::lean_ctor_set(v___x_3616_, 7, v_openDecls_3605_);
                leanh::lean_ctor_set(v___x_3616_, 8, v_initHeartbeats_3606_);
                leanh::lean_ctor_set(v___x_3616_, 9, v_maxHeartbeats_3607_);
                leanh::lean_ctor_set(v___x_3616_, 10, v_quotContext_3608_);
                leanh::lean_ctor_set(v___x_3616_, 11, v_currMacroScope_3609_);
                leanh::lean_ctor_set(v___x_3616_, 12, v_cancelTk_x3f_3610_);
                leanh::lean_ctor_set(v___x_3616_, 13, v_inheritedTraceOptions_3612_);
                leanh::lean_ctor_set_uint8(
                    v___x_3616_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_3598_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3616_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3611_,
                );
                leanh::lean_inc_ref(v_a_3523_);
                v___x_3617_ = l_Lean_Meta_check(
                    v_a_3523_,
                    v___x_3524_,
                    v___y_3526_,
                    v___y_3527_,
                    v___x_3616_,
                    v___y_3613_,
                );
                if leanh::lean_obj_tag(v___x_3617_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3617_, 1);
                    v___x_3618_ = lean_st_ref_get(v___y_3527_);
                    v___x_3619_ = lean_st_ref_take(v___y_3527_);
                    v_mctx_3620_ = leanh::lean_ctor_get(v___x_3619_, 0);
                    v_cache_3621_ = leanh::lean_ctor_get(v___x_3619_, 1);
                    v_zetaDeltaFVarIds_3622_ = leanh::lean_ctor_get(v___x_3619_, 2);
                    v_postponed_3623_ = leanh::lean_ctor_get(v___x_3619_, 3);
                    v_isSharedCheck_3647_ = (!leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3647_ == 0 {
                        v_unused_3648_ = leanh::lean_ctor_get(v___x_3619_, 4);
                        leanh::lean_dec(v_unused_3648_);
                        v___x_3625_ = v___x_3619_;
                        v_isShared_3626_ = v_isSharedCheck_3647_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_postponed_3623_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3622_);
                        leanh::lean_inc(v_cache_3621_);
                        leanh::lean_inc(v_mctx_3620_);
                        leanh::lean_dec(v___x_3619_);
                        v___x_3625_ = leanh::lean_box(0);
                        v_isShared_3626_ = v_isSharedCheck_3647_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3616_, 14);
                    leanh::lean_dec_ref(v_diag_3525_);
                    leanh::lean_dec_ref(v_a_3523_);
                    leanh::lean_dec_ref(v_kind_3521_);
                    v_a_3649_ = leanh::lean_ctor_get(v___x_3617_, 0);
                    leanh::lean_inc(v_a_3649_);
                    leanh::lean_dec_ref_known(v___x_3617_, 1);
                    v___x_3650_ = l_Lean_Exception_isInterrupt(v_a_3649_);
                    if v___x_3650_ == 0 {
                        leanh::lean_inc(v_a_3649_);
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
                    leanh::lean_ctor_set(v___x_3625_, 4, v_diag_3525_);
                    v___x_3628_ = v___x_3625_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_mctx_3620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_cache_3621_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3646_,
                        2,
                        v_zetaDeltaFVarIds_3622_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 3, v_postponed_3623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 4, v_diag_3525_);
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
                leanh::lean_dec_ref_known(v___x_3616_, 14);
                if leanh::lean_obj_tag(v___x_3631_) == 0 {
                    leanh::lean_dec(v___x_3618_);
                    leanh::lean_dec_ref(v_kind_3521_);
                    v_isSharedCheck_3639_ = (!leanh::lean_is_exclusive(v___x_3631_)) as u8;
                    if v_isSharedCheck_3639_ == 0 {
                        v_unused_3640_ = leanh::lean_ctor_get(v___x_3631_, 0);
                        leanh::lean_dec(v_unused_3640_);
                        v___x_3633_ = v___x_3631_;
                        v_isShared_3634_ = v_isSharedCheck_3639_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3631_);
                        v___x_3633_ = leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3639_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_diag_3641_ = leanh::lean_ctor_get(v___x_3618_, 4);
                    leanh::lean_inc_ref(v_diag_3641_);
                    leanh::lean_dec(v___x_3618_);
                    v_a_3642_ = leanh::lean_ctor_get(v___x_3631_, 0);
                    leanh::lean_inc(v_a_3642_);
                    leanh::lean_dec_ref_known(v___x_3631_, 1);
                    v_unfoldCounter_3643_ = leanh::lean_ctor_get(v_diag_3641_, 0);
                    leanh::lean_inc_ref(v_unfoldCounter_3643_);
                    leanh::lean_dec_ref(v_diag_3641_);
                    v___x_3644_ = l_Lean_Exception_isInterrupt(v_a_3642_);
                    if v___x_3644_ == 0 {
                        leanh::lean_inc(v_a_3642_);
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
                v___x_3635_ = leanh::lean_box(0);
                if v_isShared_3634_ == 0 {
                    leanh::lean_ctor_set(v___x_3633_, 0, v___x_3635_);
                    v___x_3637_ = v___x_3633_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
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
                    v_env_3655_ = leanh::lean_ctor_get(v___x_3654_, 0);
                    v_nextMacroScope_3656_ = leanh::lean_ctor_get(v___x_3654_, 1);
                    v_ngen_3657_ = leanh::lean_ctor_get(v___x_3654_, 2);
                    v_auxDeclNGen_3658_ = leanh::lean_ctor_get(v___x_3654_, 3);
                    v_traceState_3659_ = leanh::lean_ctor_get(v___x_3654_, 4);
                    v_messages_3660_ = leanh::lean_ctor_get(v___x_3654_, 6);
                    v_infoState_3661_ = leanh::lean_ctor_get(v___x_3654_, 7);
                    v_snapshotTasks_3662_ = leanh::lean_ctor_get(v___x_3654_, 8);
                    v_isSharedCheck_3672_ = (!leanh::lean_is_exclusive(v___x_3654_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v_unused_3673_ = leanh::lean_ctor_get(v___x_3654_, 5);
                        leanh::lean_dec(v_unused_3673_);
                        v___x_3664_ = v___x_3654_;
                        v_isShared_3665_ = v_isSharedCheck_3672_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_3662_);
                        leanh::lean_inc(v_infoState_3661_);
                        leanh::lean_inc(v_messages_3660_);
                        leanh::lean_inc(v_traceState_3659_);
                        leanh::lean_inc(v_auxDeclNGen_3658_);
                        leanh::lean_inc(v_ngen_3657_);
                        leanh::lean_inc(v_nextMacroScope_3656_);
                        leanh::lean_inc(v_env_3655_);
                        leanh::lean_dec(v___x_3654_);
                        v___x_3664_ = leanh::lean_box(0);
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
                v___x_3667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15);
                if v_isShared_3665_ == 0 {
                    leanh::lean_ctor_set(v___x_3664_, 5, v___x_3667_);
                    leanh::lean_ctor_set(v___x_3664_, 0, v___x_3666_);
                    v___x_3669_ = v___x_3664_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_nextMacroScope_3656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_ngen_3657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_auxDeclNGen_3658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 4, v_traceState_3659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 5, v___x_3667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 6, v_messages_3660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 7, v_infoState_3661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 8, v_snapshotTasks_3662_);
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
    mut v_a_3675_: *mut leanh::LeanObject,
    mut v_kind_3676_: *mut leanh::LeanObject,
    mut v___x_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
    mut v___x_3679_: *mut leanh::LeanObject,
    mut v_diag_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
    mut v___y_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_30843__boxed_3686_: u8 = 0;
    let mut v___x_30846__boxed_3687_: u8 = 0;
    let mut v_res_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_30843__boxed_3686_ = (leanh::lean_unbox(v_a_3675_) as u8);
    v___x_30846__boxed_3687_ = (leanh::lean_unbox(v___x_3679_) as u8);
    v_res_3688_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(v_a_30843__boxed_3686_, v_kind_3676_, v___x_3677_, v_a_3678_, v___x_30846__boxed_3687_, v_diag_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    leanh::lean_dec(v___y_3684_);
    leanh::lean_dec_ref(v___y_3683_);
    leanh::lean_dec(v___y_3682_);
    leanh::lean_dec_ref(v___y_3681_);
    leanh::lean_dec(v___x_3677_);
    return v_res_3688_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(
    mut v_a_3694_: u8,
    mut v_kind_3695_: *mut leanh::LeanObject,
    mut v_as_x27_3696_: *mut leanh::LeanObject,
    mut v_b_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
    mut v___y_3699_: *mut leanh::LeanObject,
    mut v___y_3700_: *mut leanh::LeanObject,
    mut v___y_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut v_unused_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3696_) == 0 {
                    leanh::lean_dec_ref(v_kind_3695_);
                    v___x_3703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3703_, 0, v_b_3697_);
                    return v___x_3703_;
                } else {
                    leanh::lean_dec_ref(v_b_3697_);
                    v_head_3704_ = leanh::lean_ctor_get(v_as_x27_3696_, 0);
                    v_tail_3705_ = leanh::lean_ctor_get(v_as_x27_3696_, 1);
                    v___x_3706_ = lean_st_ref_get(v___y_3699_);
                    v_mctx_3707_ = leanh::lean_ctor_get(v___x_3706_, 0);
                    leanh::lean_inc_ref(v_mctx_3707_);
                    leanh::lean_dec(v___x_3706_);
                    v___x_3708_ = leanh::lean_box(0);
                    v___x_3709_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0;
                    v___x_3716_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_3707_, v_head_3704_);
                    leanh::lean_dec_ref(v_mctx_3707_);
                    if leanh::lean_obj_tag(v___x_3716_) == 1 {
                        v_val_3717_ = leanh::lean_ctor_get(v___x_3716_, 0);
                        leanh::lean_inc(v_val_3717_);
                        leanh::lean_dec_ref_known(v___x_3716_, 1);
                        v_lctx_3718_ = leanh::lean_ctor_get(v_val_3717_, 1);
                        leanh::lean_inc_ref(v_lctx_3718_);
                        v_type_3719_ = leanh::lean_ctor_get(v_val_3717_, 2);
                        leanh::lean_inc_ref(v_type_3719_);
                        leanh::lean_dec(v_val_3717_);
                        v___x_3720_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_3719_, v___y_3699_);
                        v_a_3721_ = leanh::lean_ctor_get(v___x_3720_, 0);
                        leanh::lean_inc(v_a_3721_);
                        leanh::lean_dec_ref(v___x_3720_);
                        v___x_3722_ = lean_st_ref_get(v___y_3699_);
                        v_diag_3723_ = leanh::lean_ctor_get(v___x_3722_, 4);
                        leanh::lean_inc_ref_n(v_diag_3723_, 2);
                        leanh::lean_dec(v___x_3722_);
                        v___x_3724_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3725_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1;
                        v___x_3726_ = 1;
                        v___x_3727_ = leanh::lean_box((v_a_3694_) as usize);
                        v___x_3728_ = leanh::lean_box((v___x_3726_) as usize);
                        leanh::lean_inc_ref(v_kind_3695_);
                        v___f_3729_ = leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                        leanh::lean_closure_set(v___f_3729_, 0, v___x_3727_);
                        leanh::lean_closure_set(v___f_3729_, 1, v_kind_3695_);
                        leanh::lean_closure_set(v___f_3729_, 2, v___x_3724_);
                        leanh::lean_closure_set(v___f_3729_, 3, v_a_3721_);
                        leanh::lean_closure_set(v___f_3729_, 4, v___x_3728_);
                        leanh::lean_closure_set(v___f_3729_, 5, v_diag_3723_);
                        v___x_3730_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_3718_, v___x_3725_, v___f_3729_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
                        if leanh::lean_obj_tag(v___x_3730_) == 0 {
                            v_a_3731_ = leanh::lean_ctor_get(v___x_3730_, 0);
                            leanh::lean_inc(v_a_3731_);
                            leanh::lean_dec_ref_known(v___x_3730_, 1);
                            v___x_3732_ = lean_st_ref_take(v___y_3699_);
                            v_mctx_3733_ = leanh::lean_ctor_get(v___x_3732_, 0);
                            v_cache_3734_ = leanh::lean_ctor_get(v___x_3732_, 1);
                            v_zetaDeltaFVarIds_3735_ = leanh::lean_ctor_get(v___x_3732_, 2);
                            v_postponed_3736_ = leanh::lean_ctor_get(v___x_3732_, 3);
                            v_isSharedCheck_3744_ =
                                (!leanh::lean_is_exclusive(v___x_3732_)) as u8;
                            if v_isSharedCheck_3744_ == 0 {
                                v_unused_3745_ = leanh::lean_ctor_get(v___x_3732_, 4);
                                leanh::lean_dec(v_unused_3745_);
                                v___x_3738_ = v___x_3732_;
                                v_isShared_3739_ = v_isSharedCheck_3744_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_postponed_3736_);
                                leanh::lean_inc(v_zetaDeltaFVarIds_3735_);
                                leanh::lean_inc(v_cache_3734_);
                                leanh::lean_inc(v_mctx_3733_);
                                leanh::lean_dec(v___x_3732_);
                                v___x_3738_ = leanh::lean_box(0);
                                v_isShared_3739_ = v_isSharedCheck_3744_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_diag_3723_);
                            if leanh::lean_obj_tag(v___x_3730_) == 0 {
                                v_a_3746_ = leanh::lean_ctor_get(v___x_3730_, 0);
                                leanh::lean_inc(v_a_3746_);
                                leanh::lean_dec_ref_known(v___x_3730_, 1);
                                v_a_3711_ = v_a_3746_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_kind_3695_);
                                v_a_3747_ = leanh::lean_ctor_get(v___x_3730_, 0);
                                v_isSharedCheck_3754_ =
                                    (!leanh::lean_is_exclusive(v___x_3730_)) as u8;
                                if v_isSharedCheck_3754_ == 0 {
                                    v___x_3749_ = v___x_3730_;
                                    v_isShared_3750_ = v_isSharedCheck_3754_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3747_);
                                    leanh::lean_dec(v___x_3730_);
                                    v___x_3749_ = leanh::lean_box(0);
                                    v_isShared_3750_ = v_isSharedCheck_3754_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3716_);
                        v_as_x27_3696_ = v_tail_3705_;
                        v_b_3697_ = v___x_3709_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3711_) == 1 {
                    leanh::lean_dec_ref(v_kind_3695_);
                    v___x_3712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3712_, 0, v_a_3711_);
                    v___x_3713_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3713_, 0, v___x_3712_);
                    leanh::lean_ctor_set(v___x_3713_, 1, v___x_3708_);
                    v___x_3714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3714_, 0, v___x_3713_);
                    return v___x_3714_;
                } else {
                    leanh::lean_dec(v_a_3711_);
                    v_as_x27_3696_ = v_tail_3705_;
                    v_b_3697_ = v___x_3709_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_3739_ == 0 {
                    leanh::lean_ctor_set(v___x_3738_, 4, v_diag_3723_);
                    v___x_3741_ = v___x_3738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3743_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_mctx_3733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_cache_3734_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3743_,
                        2,
                        v_zetaDeltaFVarIds_3735_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_postponed_3736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 4, v_diag_3723_);
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
                    v_reuseFailAlloc_3753_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
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
    mut v_a_3756_: *mut leanh::LeanObject,
    mut v_kind_3757_: *mut leanh::LeanObject,
    mut v_as_x27_3758_: *mut leanh::LeanObject,
    mut v_b_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_31106__boxed_3765_: u8 = 0;
    let mut v_res_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_31106__boxed_3765_ = (leanh::lean_unbox(v_a_3756_) as u8);
    v_res_3766_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_31106__boxed_3765_, v_kind_3757_, v_as_x27_3758_, v_b_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
    leanh::lean_dec(v___y_3763_);
    leanh::lean_dec_ref(v___y_3762_);
    leanh::lean_dec(v___y_3761_);
    leanh::lean_dec_ref(v___y_3760_);
    leanh::lean_dec(v_as_x27_3758_);
    return v_res_3766_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(
    mut v_a_3767_: u8,
    mut v_kind_3768_: *mut leanh::LeanObject,
    mut v_goals_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
    mut v___y_3773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v_fst_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_a_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3775_ = leanh::lean_box(0);
                v___x_3776_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0;
                v___x_3777_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_3767_, v_kind_3768_, v_goals_3769_, v___x_3776_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
                if leanh::lean_obj_tag(v___x_3777_) == 0 {
                    v_a_3778_ = leanh::lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3790_ = (!leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3780_ = v___x_3777_;
                        v_isShared_3781_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3778_);
                        leanh::lean_dec(v___x_3777_);
                        v___x_3780_ = leanh::lean_box(0);
                        v_isShared_3781_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3791_ = leanh::lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3798_ = (!leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3798_ == 0 {
                        v___x_3793_ = v___x_3777_;
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3791_);
                        leanh::lean_dec(v___x_3777_);
                        v___x_3793_ = leanh::lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3782_ = leanh::lean_ctor_get(v_a_3778_, 0);
                leanh::lean_inc(v_fst_3782_);
                leanh::lean_dec(v_a_3778_);
                if leanh::lean_obj_tag(v_fst_3782_) == 0 {
                    if v_isShared_3781_ == 0 {
                        leanh::lean_ctor_set(v___x_3780_, 0, v___x_3775_);
                        v___x_3784_ = v___x_3780_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3775_);
                        v___x_3784_ = v_reuseFailAlloc_3785_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3786_ = leanh::lean_ctor_get(v_fst_3782_, 0);
                    leanh::lean_inc(v_val_3786_);
                    leanh::lean_dec_ref_known(v_fst_3782_, 1);
                    if v_isShared_3781_ == 0 {
                        leanh::lean_ctor_set(v___x_3780_, 0, v_val_3786_);
                        v___x_3788_ = v___x_3780_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_val_3786_);
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
                    v_reuseFailAlloc_3797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
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
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_kind_3800_: *mut leanh::LeanObject,
    mut v_goals_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
    mut v___y_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_31224__boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_31224__boxed_3807_ = (leanh::lean_unbox(v_a_3799_) as u8);
    v_res_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(v_a_31224__boxed_3807_, v_kind_3800_, v_goals_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
    leanh::lean_dec(v___y_3805_);
    leanh::lean_dec_ref(v___y_3804_);
    leanh::lean_dec(v___y_3803_);
    leanh::lean_dec_ref(v___y_3802_);
    leanh::lean_dec(v_goals_3801_);
    return v_res_3808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(
    mut v_a_3809_: u8,
    mut v_val_3810_: *mut leanh::LeanObject,
    mut v_as_3811_: *mut leanh::LeanObject,
    mut v_sz_3812_: usize,
    mut v_i_3813_: usize,
    mut v_b_3814_: *mut leanh::LeanObject,
    mut v___y_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3818_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
                if v___x_3818_ == 0 {
                    leanh::lean_dec(v_val_3810_);
                    v___x_3819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3819_, 0, v_b_3814_);
                    return v___x_3819_;
                } else {
                    v___x_3820_ = leanh::lean_box((v_a_3809_) as usize);
                    v___f_3821_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    leanh::lean_closure_set(v___f_3821_, 0, v___x_3820_);
                    v___x_3822_ = leanh::lean_box((v_a_3809_) as usize);
                    v___f_3823_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_3823_, 0, v___x_3822_);
                    v___x_3824_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
                    v___x_3825_ = leanh::lean_box((v_a_3809_) as usize);
                    leanh::lean_inc(v_val_3810_);
                    v___f_3826_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed as *mut core::ffi::c_void, 10, 4);
                    leanh::lean_closure_set(v___f_3826_, 0, v_val_3810_);
                    leanh::lean_closure_set(v___f_3826_, 1, v___x_3825_);
                    leanh::lean_closure_set(v___f_3826_, 2, v___x_3824_);
                    leanh::lean_closure_set(v___f_3826_, 3, v___f_3821_);
                    v_a_3827_ = lean_array_uget_borrowed(v_as_3811_, v_i_3813_);
                    v___x_3828_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_3827_);
                    v___x_3829_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___f_3823_, v___f_3826_, v___x_3828_, v_a_3827_, v___y_3815_, v___y_3816_);
                    if leanh::lean_obj_tag(v___x_3829_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3829_, 1);
                        v___x_3830_ = leanh::lean_box(0);
                        v___x_3831_ = 1usize;
                        v___x_3832_ = lean_usize_add(v_i_3813_, v___x_3831_);
                        v_i_3813_ = v___x_3832_;
                        v_b_3814_ = v___x_3830_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_3810_);
                        return v___x_3829_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_val_3835_: *mut leanh::LeanObject,
    mut v_as_3836_: *mut leanh::LeanObject,
    mut v_sz_3837_: *mut leanh::LeanObject,
    mut v_i_3838_: *mut leanh::LeanObject,
    mut v_b_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_31289__boxed_3843_: u8 = 0;
    let mut v_sz_boxed_3844_: usize = 0;
    let mut v_i_boxed_3845_: usize = 0;
    let mut v_res_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_31289__boxed_3843_ = (leanh::lean_unbox(v_a_3834_) as u8);
    v_sz_boxed_3844_ = leanh::lean_unbox_usize(v_sz_3837_);
    leanh::lean_dec(v_sz_3837_);
    v_i_boxed_3845_ = leanh::lean_unbox_usize(v_i_3838_);
    leanh::lean_dec(v_i_3838_);
    v_res_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v_a_31289__boxed_3843_, v_val_3835_, v_as_3836_, v_sz_boxed_3844_, v_i_boxed_3845_, v_b_3839_, v___y_3840_, v___y_3841_);
    leanh::lean_dec(v___y_3841_);
    leanh::lean_dec_ref(v___y_3840_);
    leanh::lean_dec_ref(v_as_3836_);
    return v_res_3846_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(
    mut v___cmdStx_3847_: *mut leanh::LeanObject,
    mut v___y_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3856_: u8 = 0;
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3870_: usize = 0;
    let mut v___x_3871_: usize = 0;
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_unused_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3851_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
                v___x_3852_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_3851_, v___y_3849_);
                v_a_3853_ = leanh::lean_ctor_get(v___x_3852_, 0);
                v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v___x_3852_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v___x_3855_ = v___x_3852_;
                    v_isShared_3856_ = v_isSharedCheck_3882_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3853_);
                    leanh::lean_dec(v___x_3852_);
                    v___x_3855_ = leanh::lean_box(0);
                    v_isShared_3856_ = v_isSharedCheck_3882_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3857_ = (leanh::lean_unbox(v_a_3853_) as u8);
                if v___x_3857_ == 0 {
                    leanh::lean_dec(v_a_3853_);
                    v___x_3858_ = leanh::lean_box(0);
                    if v_isShared_3856_ == 0 {
                        leanh::lean_ctor_set(v___x_3855_, 0, v___x_3858_);
                        v___x_3860_ = v___x_3855_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
                        v___x_3860_ = v_reuseFailAlloc_3861_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3855_);
                    v___x_3862_ = lean_st_ref_get(v___y_3849_);
                    v___x_3863_ = 0;
                    v___x_3864_ = leanh::lean_box((v___x_3863_) as usize);
                    v___x_3865_ = lean_st_mk_ref(v___x_3864_);
                    v_infoState_3866_ = leanh::lean_ctor_get(v___x_3862_, 8);
                    leanh::lean_inc_ref(v_infoState_3866_);
                    leanh::lean_dec(v___x_3862_);
                    v_trees_3867_ = leanh::lean_ctor_get(v_infoState_3866_, 2);
                    leanh::lean_inc_ref(v_trees_3867_);
                    leanh::lean_dec_ref(v_infoState_3866_);
                    v___x_3868_ = l_Lean_PersistentArray_toArray___redArg(v_trees_3867_);
                    leanh::lean_dec_ref(v_trees_3867_);
                    v___x_3869_ = leanh::lean_box(0);
                    v_sz_3870_ = lean_array_size(v___x_3868_);
                    v___x_3871_ = 0usize;
                    v___x_3872_ = (leanh::lean_unbox(v_a_3853_) as u8);
                    leanh::lean_dec(v_a_3853_);
                    v___x_3873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v___x_3872_, v___x_3865_, v___x_3868_, v_sz_3870_, v___x_3871_, v___x_3869_, v___y_3848_, v___y_3849_);
                    leanh::lean_dec_ref(v___x_3868_);
                    if leanh::lean_obj_tag(v___x_3873_) == 0 {
                        v_isSharedCheck_3880_ =
                            (!leanh::lean_is_exclusive(v___x_3873_)) as u8;
                        if v_isSharedCheck_3880_ == 0 {
                            v_unused_3881_ = leanh::lean_ctor_get(v___x_3873_, 0);
                            leanh::lean_dec(v_unused_3881_);
                            v___x_3875_ = v___x_3873_;
                            v_isShared_3876_ = v_isSharedCheck_3880_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3873_);
                            v___x_3875_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3875_, 0, v___x_3869_);
                    v___x_3878_ = v___x_3875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3869_);
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
    mut v___cmdStx_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
    mut v___y_3885_: *mut leanh::LeanObject,
    mut v___y_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ =
        l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(
            v___cmdStx_3883_,
            v___y_3884_,
            v___y_3885_,
        );
    leanh::lean_dec(v___y_3885_);
    leanh::lean_dec_ref(v___y_3884_);
    leanh::lean_dec(v___cmdStx_3883_);
    return v_res_3887_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(
    mut v_opt_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_3896_, v___y_3898_);
    return v___x_3900_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(
    mut v_opt_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3905_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_3901_, v___y_3902_, v___y_3903_);
    leanh::lean_dec(v___y_3903_);
    leanh::lean_dec_ref(v___y_3902_);
    leanh::lean_dec_ref(v_opt_3901_);
    return v_res_3905_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(
    mut v_00_u03b2_3906_: *mut leanh::LeanObject,
    mut v_m_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3908_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_3907_);
    return v___x_3908_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(
    mut v_00_u03b2_3909_: *mut leanh::LeanObject,
    mut v_m_3910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3911_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_00_u03b2_3909_, v_m_3910_);
    leanh::lean_dec_ref(v_m_3910_);
    return v_res_3911_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(
    mut v_a_3912_: u8,
    mut v_kind_3913_: *mut leanh::LeanObject,
    mut v_as_3914_: *mut leanh::LeanObject,
    mut v_as_x27_3915_: *mut leanh::LeanObject,
    mut v_b_3916_: *mut leanh::LeanObject,
    mut v_a_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
    mut v___y_3919_: *mut leanh::LeanObject,
    mut v___y_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_3912_, v_kind_3913_, v_as_x27_3915_, v_b_3916_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
    return v___x_3923_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(
    mut v_a_3924_: *mut leanh::LeanObject,
    mut v_kind_3925_: *mut leanh::LeanObject,
    mut v_as_3926_: *mut leanh::LeanObject,
    mut v_as_x27_3927_: *mut leanh::LeanObject,
    mut v_b_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_31468__boxed_3935_: u8 = 0;
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_31468__boxed_3935_ = (leanh::lean_unbox(v_a_3924_) as u8);
    v_res_3936_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_a_31468__boxed_3935_, v_kind_3925_, v_as_3926_, v_as_x27_3927_, v_b_3928_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
    leanh::lean_dec(v___y_3933_);
    leanh::lean_dec_ref(v___y_3932_);
    leanh::lean_dec(v___y_3931_);
    leanh::lean_dec_ref(v___y_3930_);
    leanh::lean_dec(v_as_x27_3927_);
    leanh::lean_dec(v_as_3926_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(
    mut v_00_u03b2_3937_: *mut leanh::LeanObject,
    mut v_x_3938_: *mut leanh::LeanObject,
    mut v_x_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3940_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_3938_, v_x_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(
    mut v_00_u03b2_3941_: *mut leanh::LeanObject,
    mut v_x_3942_: *mut leanh::LeanObject,
    mut v_x_3943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(v_00_u03b2_3941_, v_x_3942_, v_x_3943_);
    leanh::lean_dec(v_x_3943_);
    leanh::lean_dec_ref(v_x_3942_);
    return v_res_3944_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(
    mut v_00_u03b2_3945_: *mut leanh::LeanObject,
    mut v_x_3946_: *mut leanh::LeanObject,
    mut v_x_3947_: *mut leanh::LeanObject,
    mut v_x_3948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_x_3946_, v_x_3947_, v_x_3948_);
    return v___x_3949_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(
    mut v_00_u03c3_3950_: *mut leanh::LeanObject,
    mut v_00_u03b2_3951_: *mut leanh::LeanObject,
    mut v_map_3952_: *mut leanh::LeanObject,
    mut v_init_3953_: *mut leanh::LeanObject,
    mut v_f_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_3952_, v_init_3953_, v_f_3954_);
    return v___x_3955_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(
    mut v_00_u03c3_3956_: *mut leanh::LeanObject,
    mut v_00_u03b2_3957_: *mut leanh::LeanObject,
    mut v_map_3958_: *mut leanh::LeanObject,
    mut v_init_3959_: *mut leanh::LeanObject,
    mut v_f_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(v_00_u03c3_3956_, v_00_u03b2_3957_, v_map_3958_, v_init_3959_, v_f_3960_);
    leanh::lean_dec_ref(v_map_3958_);
    return v_res_3961_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(
    mut v_00_u03c3_3962_: *mut leanh::LeanObject,
    mut v_00_u03b2_3963_: *mut leanh::LeanObject,
    mut v_map_3964_: *mut leanh::LeanObject,
    mut v_f_3965_: *mut leanh::LeanObject,
    mut v_init_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_3964_, v_f_3965_, v_init_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(
    mut v_00_u03c3_3968_: *mut leanh::LeanObject,
    mut v_00_u03b2_3969_: *mut leanh::LeanObject,
    mut v_map_3970_: *mut leanh::LeanObject,
    mut v_f_3971_: *mut leanh::LeanObject,
    mut v_init_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(v_00_u03c3_3968_, v_00_u03b2_3969_, v_map_3970_, v_f_3971_, v_init_3972_);
    leanh::lean_dec_ref(v_map_3970_);
    return v_res_3973_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(
    mut v_00_u03b1_3974_: *mut leanh::LeanObject,
    mut v_msg_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_3975_, v___y_3976_, v___y_3977_);
    return v___x_3979_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(
    mut v_00_u03b1_3980_: *mut leanh::LeanObject,
    mut v_msg_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(v_00_u03b1_3980_, v_msg_3981_, v___y_3982_, v___y_3983_);
    leanh::lean_dec(v___y_3983_);
    leanh::lean_dec_ref(v___y_3982_);
    return v_res_3985_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(
    mut v_00_u03b1_3986_: *mut leanh::LeanObject,
    mut v_preNode_3987_: *mut leanh::LeanObject,
    mut v_postNode_3988_: *mut leanh::LeanObject,
    mut v_x_3989_: *mut leanh::LeanObject,
    mut v_x_3990_: *mut leanh::LeanObject,
    mut v___y_3991_: *mut leanh::LeanObject,
    mut v___y_3992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_3987_, v_postNode_3988_, v_x_3989_, v_x_3990_, v___y_3991_, v___y_3992_);
    return v___x_3994_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(
    mut v_00_u03b1_3995_: *mut leanh::LeanObject,
    mut v_preNode_3996_: *mut leanh::LeanObject,
    mut v_postNode_3997_: *mut leanh::LeanObject,
    mut v_x_3998_: *mut leanh::LeanObject,
    mut v_x_3999_: *mut leanh::LeanObject,
    mut v___y_4000_: *mut leanh::LeanObject,
    mut v___y_4001_: *mut leanh::LeanObject,
    mut v___y_4002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(v_00_u03b1_3995_, v_preNode_3996_, v_postNode_3997_, v_x_3998_, v_x_3999_, v___y_4000_, v___y_4001_);
    leanh::lean_dec(v___y_4001_);
    leanh::lean_dec_ref(v___y_4000_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(
    mut v_00_u03b2_4004_: *mut leanh::LeanObject,
    mut v_x_4005_: *mut leanh::LeanObject,
    mut v_x_4006_: usize,
    mut v_x_4007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_4005_, v_x_4006_, v_x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(
    mut v_00_u03b2_4009_: *mut leanh::LeanObject,
    mut v_x_4010_: *mut leanh::LeanObject,
    mut v_x_4011_: *mut leanh::LeanObject,
    mut v_x_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_31540__boxed_4013_: usize = 0;
    let mut v_res_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_31540__boxed_4013_ = leanh::lean_unbox_usize(v_x_4011_);
    leanh::lean_dec(v_x_4011_);
    v_res_4014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(v_00_u03b2_4009_, v_x_4010_, v_x_31540__boxed_4013_, v_x_4012_);
    leanh::lean_dec(v_x_4012_);
    leanh::lean_dec_ref(v_x_4010_);
    return v_res_4014_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(
    mut v_00_u03b2_4015_: *mut leanh::LeanObject,
    mut v_x_4016_: *mut leanh::LeanObject,
    mut v_x_4017_: usize,
    mut v_x_4018_: usize,
    mut v_x_4019_: *mut leanh::LeanObject,
    mut v_x_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_4016_, v_x_4017_, v_x_4018_, v_x_4019_, v_x_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(
    mut v_00_u03b2_4022_: *mut leanh::LeanObject,
    mut v_x_4023_: *mut leanh::LeanObject,
    mut v_x_4024_: *mut leanh::LeanObject,
    mut v_x_4025_: *mut leanh::LeanObject,
    mut v_x_4026_: *mut leanh::LeanObject,
    mut v_x_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_31551__boxed_4028_: usize = 0;
    let mut v_x_31552__boxed_4029_: usize = 0;
    let mut v_res_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_31551__boxed_4028_ = leanh::lean_unbox_usize(v_x_4024_);
    leanh::lean_dec(v_x_4024_);
    v_x_31552__boxed_4029_ = leanh::lean_unbox_usize(v_x_4025_);
    leanh::lean_dec(v_x_4025_);
    v_res_4030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(v_00_u03b2_4022_, v_x_4023_, v_x_31551__boxed_4028_, v_x_31552__boxed_4029_, v_x_4026_, v_x_4027_);
    return v_res_4030_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(
    mut v_map_4031_: *mut leanh::LeanObject,
    mut v_f_4032_: *mut leanh::LeanObject,
    mut v_init_4033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4032_, v_map_4031_, v_init_4033_);
    return v___x_4034_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(
    mut v_00_u03c3_4035_: *mut leanh::LeanObject,
    mut v_00_u03c3_4036_: *mut leanh::LeanObject,
    mut v_00_u03b2_4037_: *mut leanh::LeanObject,
    mut v_map_4038_: *mut leanh::LeanObject,
    mut v_f_4039_: *mut leanh::LeanObject,
    mut v_init_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4039_, v_map_4038_, v_init_4040_);
    return v___x_4041_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(
    mut v_map_4042_: *mut leanh::LeanObject,
    mut v_f_4043_: *mut leanh::LeanObject,
    mut v_init_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4043_, v_map_4042_, v_init_4044_);
    return v___x_4045_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(
    mut v_map_4046_: *mut leanh::LeanObject,
    mut v_f_4047_: *mut leanh::LeanObject,
    mut v_init_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(v_map_4046_, v_f_4047_, v_init_4048_);
    leanh::lean_dec_ref(v_map_4046_);
    return v_res_4049_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(
    mut v_00_u03c3_4050_: *mut leanh::LeanObject,
    mut v_00_u03b2_4051_: *mut leanh::LeanObject,
    mut v_map_4052_: *mut leanh::LeanObject,
    mut v_f_4053_: *mut leanh::LeanObject,
    mut v_init_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4053_, v_map_4052_, v_init_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(
    mut v_00_u03c3_4056_: *mut leanh::LeanObject,
    mut v_00_u03b2_4057_: *mut leanh::LeanObject,
    mut v_map_4058_: *mut leanh::LeanObject,
    mut v_f_4059_: *mut leanh::LeanObject,
    mut v_init_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(v_00_u03c3_4056_, v_00_u03b2_4057_, v_map_4058_, v_f_4059_, v_init_4060_);
    leanh::lean_dec_ref(v_map_4058_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(
    mut v_msgData_4062_: *mut leanh::LeanObject,
    mut v___y_4063_: *mut leanh::LeanObject,
    mut v___y_4064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_4062_, v___y_4064_);
    return v___x_4066_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(
    mut v_msgData_4067_: *mut leanh::LeanObject,
    mut v___y_4068_: *mut leanh::LeanObject,
    mut v___y_4069_: *mut leanh::LeanObject,
    mut v___y_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(v_msgData_4067_, v___y_4068_, v___y_4069_);
    leanh::lean_dec(v___y_4069_);
    leanh::lean_dec_ref(v___y_4068_);
    return v_res_4071_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(
    mut v_00_u03b1_4072_: *mut leanh::LeanObject,
    mut v_preNode_4073_: *mut leanh::LeanObject,
    mut v_postNode_4074_: *mut leanh::LeanObject,
    mut v___x_4075_: *mut leanh::LeanObject,
    mut v_x_4076_: *mut leanh::LeanObject,
    mut v_x_4077_: *mut leanh::LeanObject,
    mut v___y_4078_: *mut leanh::LeanObject,
    mut v___y_4079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4081_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_4073_, v_postNode_4074_, v___x_4075_, v_x_4076_, v_x_4077_, v___y_4078_, v___y_4079_);
    return v___x_4081_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(
    mut v_00_u03b1_4082_: *mut leanh::LeanObject,
    mut v_preNode_4083_: *mut leanh::LeanObject,
    mut v_postNode_4084_: *mut leanh::LeanObject,
    mut v___x_4085_: *mut leanh::LeanObject,
    mut v_x_4086_: *mut leanh::LeanObject,
    mut v_x_4087_: *mut leanh::LeanObject,
    mut v___y_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(v_00_u03b1_4082_, v_preNode_4083_, v_postNode_4084_, v___x_4085_, v_x_4086_, v_x_4087_, v___y_4088_, v___y_4089_);
    leanh::lean_dec(v___y_4089_);
    leanh::lean_dec_ref(v___y_4088_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(
    mut v_00_u03b2_4092_: *mut leanh::LeanObject,
    mut v_keys_4093_: *mut leanh::LeanObject,
    mut v_vals_4094_: *mut leanh::LeanObject,
    mut v_heq_4095_: *mut leanh::LeanObject,
    mut v_i_4096_: *mut leanh::LeanObject,
    mut v_k_4097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_4093_, v_vals_4094_, v_i_4096_, v_k_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(
    mut v_00_u03b2_4099_: *mut leanh::LeanObject,
    mut v_keys_4100_: *mut leanh::LeanObject,
    mut v_vals_4101_: *mut leanh::LeanObject,
    mut v_heq_4102_: *mut leanh::LeanObject,
    mut v_i_4103_: *mut leanh::LeanObject,
    mut v_k_4104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4105_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(v_00_u03b2_4099_, v_keys_4100_, v_vals_4101_, v_heq_4102_, v_i_4103_, v_k_4104_);
    leanh::lean_dec(v_k_4104_);
    leanh::lean_dec_ref(v_vals_4101_);
    leanh::lean_dec_ref(v_keys_4100_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(
    mut v_00_u03b2_4106_: *mut leanh::LeanObject,
    mut v_n_4107_: *mut leanh::LeanObject,
    mut v_k_4108_: *mut leanh::LeanObject,
    mut v_v_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v_n_4107_, v_k_4108_, v_v_4109_);
    return v___x_4110_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(
    mut v_00_u03b2_4111_: *mut leanh::LeanObject,
    mut v_depth_4112_: usize,
    mut v_keys_4113_: *mut leanh::LeanObject,
    mut v_vals_4114_: *mut leanh::LeanObject,
    mut v_heq_4115_: *mut leanh::LeanObject,
    mut v_i_4116_: *mut leanh::LeanObject,
    mut v_entries_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_4112_, v_keys_4113_, v_vals_4114_, v_i_4116_, v_entries_4117_);
    return v___x_4118_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(
    mut v_00_u03b2_4119_: *mut leanh::LeanObject,
    mut v_depth_4120_: *mut leanh::LeanObject,
    mut v_keys_4121_: *mut leanh::LeanObject,
    mut v_vals_4122_: *mut leanh::LeanObject,
    mut v_heq_4123_: *mut leanh::LeanObject,
    mut v_i_4124_: *mut leanh::LeanObject,
    mut v_entries_4125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4126_: usize = 0;
    let mut v_res_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4126_ = leanh::lean_unbox_usize(v_depth_4120_);
    leanh::lean_dec(v_depth_4120_);
    v_res_4127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(v_00_u03b2_4119_, v_depth_boxed_4126_, v_keys_4121_, v_vals_4122_, v_heq_4123_, v_i_4124_, v_entries_4125_);
    leanh::lean_dec_ref(v_vals_4122_);
    leanh::lean_dec_ref(v_keys_4121_);
    return v_res_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(
    mut v_00_u03c3_4128_: *mut leanh::LeanObject,
    mut v_00_u03c3_4129_: *mut leanh::LeanObject,
    mut v_00_u03b1_4130_: *mut leanh::LeanObject,
    mut v_00_u03b2_4131_: *mut leanh::LeanObject,
    mut v_f_4132_: *mut leanh::LeanObject,
    mut v_x_4133_: *mut leanh::LeanObject,
    mut v_x_4134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_4132_, v_x_4133_, v_x_4134_);
    return v___x_4135_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(
    mut v_00_u03c3_4136_: *mut leanh::LeanObject,
    mut v_00_u03b1_4137_: *mut leanh::LeanObject,
    mut v_00_u03b2_4138_: *mut leanh::LeanObject,
    mut v_f_4139_: *mut leanh::LeanObject,
    mut v_x_4140_: *mut leanh::LeanObject,
    mut v_x_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_4139_, v_x_4140_, v_x_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(
    mut v_00_u03c3_4143_: *mut leanh::LeanObject,
    mut v_00_u03b1_4144_: *mut leanh::LeanObject,
    mut v_00_u03b2_4145_: *mut leanh::LeanObject,
    mut v_f_4146_: *mut leanh::LeanObject,
    mut v_x_4147_: *mut leanh::LeanObject,
    mut v_x_4148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(v_00_u03c3_4143_, v_00_u03b1_4144_, v_00_u03b2_4145_, v_f_4146_, v_x_4147_, v_x_4148_);
    leanh::lean_dec_ref(v_x_4147_);
    return v_res_4149_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(
    mut v_00_u03b2_4150_: *mut leanh::LeanObject,
    mut v_x_4151_: *mut leanh::LeanObject,
    mut v_x_4152_: *mut leanh::LeanObject,
    mut v_x_4153_: *mut leanh::LeanObject,
    mut v_x_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4155_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_x_4151_, v_x_4152_, v_x_4153_, v_x_4154_);
    return v___x_4155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(
    mut v_00_u03b1_4156_: *mut leanh::LeanObject,
    mut v_00_u03b2_4157_: *mut leanh::LeanObject,
    mut v_00_u03c3_4158_: *mut leanh::LeanObject,
    mut v_00_u03c3_4159_: *mut leanh::LeanObject,
    mut v_f_4160_: *mut leanh::LeanObject,
    mut v_as_4161_: *mut leanh::LeanObject,
    mut v_i_4162_: usize,
    mut v_stop_4163_: usize,
    mut v_b_4164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_4160_, v_as_4161_, v_i_4162_, v_stop_4163_, v_b_4164_);
    return v___x_4165_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(
    mut v_00_u03b1_4166_: *mut leanh::LeanObject,
    mut v_00_u03b2_4167_: *mut leanh::LeanObject,
    mut v_00_u03c3_4168_: *mut leanh::LeanObject,
    mut v_00_u03c3_4169_: *mut leanh::LeanObject,
    mut v_f_4170_: *mut leanh::LeanObject,
    mut v_as_4171_: *mut leanh::LeanObject,
    mut v_i_4172_: *mut leanh::LeanObject,
    mut v_stop_4173_: *mut leanh::LeanObject,
    mut v_b_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4175_: usize = 0;
    let mut v_stop_boxed_4176_: usize = 0;
    let mut v_res_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4175_ = leanh::lean_unbox_usize(v_i_4172_);
    leanh::lean_dec(v_i_4172_);
    v_stop_boxed_4176_ = leanh::lean_unbox_usize(v_stop_4173_);
    leanh::lean_dec(v_stop_4173_);
    v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(v_00_u03b1_4166_, v_00_u03b2_4167_, v_00_u03c3_4168_, v_00_u03c3_4169_, v_f_4170_, v_as_4171_, v_i_boxed_4175_, v_stop_boxed_4176_, v_b_4174_);
    leanh::lean_dec_ref(v_as_4171_);
    return v_res_4177_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(
    mut v_00_u03c3_4178_: *mut leanh::LeanObject,
    mut v_00_u03c3_4179_: *mut leanh::LeanObject,
    mut v_00_u03b1_4180_: *mut leanh::LeanObject,
    mut v_00_u03b2_4181_: *mut leanh::LeanObject,
    mut v_f_4182_: *mut leanh::LeanObject,
    mut v_keys_4183_: *mut leanh::LeanObject,
    mut v_vals_4184_: *mut leanh::LeanObject,
    mut v_heq_4185_: *mut leanh::LeanObject,
    mut v_i_4186_: *mut leanh::LeanObject,
    mut v_acc_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_4182_, v_keys_4183_, v_vals_4184_, v_i_4186_, v_acc_4187_);
    return v___x_4188_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(
    mut v_00_u03c3_4189_: *mut leanh::LeanObject,
    mut v_00_u03c3_4190_: *mut leanh::LeanObject,
    mut v_00_u03b1_4191_: *mut leanh::LeanObject,
    mut v_00_u03b2_4192_: *mut leanh::LeanObject,
    mut v_f_4193_: *mut leanh::LeanObject,
    mut v_keys_4194_: *mut leanh::LeanObject,
    mut v_vals_4195_: *mut leanh::LeanObject,
    mut v_heq_4196_: *mut leanh::LeanObject,
    mut v_i_4197_: *mut leanh::LeanObject,
    mut v_acc_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(v_00_u03c3_4189_, v_00_u03c3_4190_, v_00_u03b1_4191_, v_00_u03b2_4192_, v_f_4193_, v_keys_4194_, v_vals_4195_, v_heq_4196_, v_i_4197_, v_acc_4198_);
    leanh::lean_dec_ref(v_vals_4195_);
    leanh::lean_dec_ref(v_keys_4194_);
    return v_res_4199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(
    mut v_00_u03b1_4200_: *mut leanh::LeanObject,
    mut v_00_u03b2_4201_: *mut leanh::LeanObject,
    mut v_00_u03c3_4202_: *mut leanh::LeanObject,
    mut v_f_4203_: *mut leanh::LeanObject,
    mut v_as_4204_: *mut leanh::LeanObject,
    mut v_i_4205_: usize,
    mut v_stop_4206_: usize,
    mut v_b_4207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_4203_, v_as_4204_, v_i_4205_, v_stop_4206_, v_b_4207_);
    return v___x_4208_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(
    mut v_00_u03b1_4209_: *mut leanh::LeanObject,
    mut v_00_u03b2_4210_: *mut leanh::LeanObject,
    mut v_00_u03c3_4211_: *mut leanh::LeanObject,
    mut v_f_4212_: *mut leanh::LeanObject,
    mut v_as_4213_: *mut leanh::LeanObject,
    mut v_i_4214_: *mut leanh::LeanObject,
    mut v_stop_4215_: *mut leanh::LeanObject,
    mut v_b_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4217_: usize = 0;
    let mut v_stop_boxed_4218_: usize = 0;
    let mut v_res_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4217_ = leanh::lean_unbox_usize(v_i_4214_);
    leanh::lean_dec(v_i_4214_);
    v_stop_boxed_4218_ = leanh::lean_unbox_usize(v_stop_4215_);
    leanh::lean_dec(v_stop_4215_);
    v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(v_00_u03b1_4209_, v_00_u03b2_4210_, v_00_u03c3_4211_, v_f_4212_, v_as_4213_, v_i_boxed_4217_, v_stop_boxed_4218_, v_b_4216_);
    leanh::lean_dec_ref(v_as_4213_);
    return v_res_4219_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(
    mut v_00_u03c3_4220_: *mut leanh::LeanObject,
    mut v_00_u03b1_4221_: *mut leanh::LeanObject,
    mut v_00_u03b2_4222_: *mut leanh::LeanObject,
    mut v_f_4223_: *mut leanh::LeanObject,
    mut v_keys_4224_: *mut leanh::LeanObject,
    mut v_vals_4225_: *mut leanh::LeanObject,
    mut v_heq_4226_: *mut leanh::LeanObject,
    mut v_i_4227_: *mut leanh::LeanObject,
    mut v_acc_4228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_4223_, v_keys_4224_, v_vals_4225_, v_i_4227_, v_acc_4228_);
    return v___x_4229_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(
    mut v_00_u03c3_4230_: *mut leanh::LeanObject,
    mut v_00_u03b1_4231_: *mut leanh::LeanObject,
    mut v_00_u03b2_4232_: *mut leanh::LeanObject,
    mut v_f_4233_: *mut leanh::LeanObject,
    mut v_keys_4234_: *mut leanh::LeanObject,
    mut v_vals_4235_: *mut leanh::LeanObject,
    mut v_heq_4236_: *mut leanh::LeanObject,
    mut v_i_4237_: *mut leanh::LeanObject,
    mut v_acc_4238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(v_00_u03c3_4230_, v_00_u03b1_4231_, v_00_u03b2_4232_, v_f_4233_, v_keys_4234_, v_vals_4235_, v_heq_4236_, v_i_4237_, v_acc_4238_);
    leanh::lean_dec_ref(v_vals_4235_);
    leanh::lean_dec_ref(v_keys_4234_);
    return v_res_4239_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances;
    v___x_4242_ = l_Lean_Elab_Command_addLinter(v___x_4241_);
    return v___x_4242_;
}
pub unsafe fn l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(
    mut v_a_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
    return v_res_4244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_TacticTypeCheck(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances,
    );
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_TacticTypeCheck(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_TacticTypeCheck(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_TacticTypeCheck(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_TacticTypeCheck(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_TacticTypeCheck(builtin);
}