// Lean compiler output
// Module: Lean.Linter.List
// Imports: Lean.Linter.Basic Lean.Server.InfoUtils Lean.Linter.Init
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_addLinter, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_ContextInfo_runMetaM___redArg, l_Lean_Elab_Info_updateContext_x3f,
    l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_linterMessageTag,
    runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_userName, lean_local_ctx_find};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, l_Lean_Elab_Info_stx,
    l_Lean_Elab_InfoTree_deepestNodes___redArg, runtime_initialize_Lean_Server_InfoUtils,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 100, 101, 120, 86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2370590245460535436 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<106> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [86, 97, 108, 105, 100, 97, 116, 101, 32, 116, 104, 97, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 40, 101, 46, 103, 46, 32, 105, 110, 32, 96, 120, 115, 91, 105, 93, 96, 32, 111, 114, 32, 96, 120, 115, 46, 116, 97, 107, 101, 32, 105, 96, 41, 32, 97, 114, 101, 32, 111, 110, 108, 121, 32, 96, 105, 96, 44, 32, 96, 106, 96, 44, 32, 111, 114, 32, 96, 107, 96, 46, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13480916849937425914 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9252344385775686671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12101741544773259677 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_linter_indexVariables: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 115, 116, 86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4853507067084237010 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [86, 97, 108, 105, 100, 97, 116, 101, 32, 116, 104, 97, 116, 32, 97, 108, 108, 32, 96, 76, 105, 115, 116, 96, 47, 96, 65, 114, 114, 97, 121, 96, 47, 96, 86, 101, 99, 116, 111, 114, 96, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 117, 115, 101, 32, 97, 108, 108, 111, 119, 101, 100, 32, 110, 97, 109, 101, 115, 46, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13480916849937425914 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9252344385775686671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12089079435222617387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_linter_listVariables: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value:
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value:
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
    m_data: [122, 105, 112, 73, 100, 120, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8467293704094663304 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value:
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
    m_data: [101, 114, 97, 115, 101, 73, 100, 120, 33, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
            as *mut crate::leanh::LeanObject,
        10802932081047211230 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value:
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
    m_data: [115, 104, 114, 105, 110, 107, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3872834428859331858 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value:
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
    m_data: [100, 114, 111, 112, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
            as *mut crate::leanh::LeanObject,
        2233317244024471518 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value:
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
    m_data: [116, 97, 107, 101, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
            as *mut crate::leanh::LeanObject,
        5193315113790084929 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16034137926423127740 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 114, 97, 115, 101, 73, 100, 120, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
            as *mut crate::leanh::LeanObject,
        1396115026687347110 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
            as *mut crate::leanh::LeanObject,
        10539643452699375210 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
            as *mut crate::leanh::LeanObject,
        16221596318437611981 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value:
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
    m_data: [86, 101, 99, 116, 111, 114, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18152428103632701704 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9925259263419088478 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
            as *mut crate::leanh::LeanObject,
        6571270745476678546 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
            as *mut crate::leanh::LeanObject,
        16343519309823643998 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
            as *mut crate::leanh::LeanObject,
        12014922020157731009 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value:
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
    m_data: [109, 111, 100, 105, 102, 121, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
            as *mut crate::leanh::LeanObject,
        5052701508307584446 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        101, 114, 97, 115, 101, 73, 100, 120, 73, 102, 73, 110, 66, 111, 117, 110, 100, 115, 0,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value)
            as *mut crate::leanh::LeanObject,
        4405791127581099400 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
            as *mut crate::leanh::LeanObject,
        18119106984202331506 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 101, 114, 116, 73, 100, 120, 33, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
            as *mut crate::leanh::LeanObject,
        10432512871714827331 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 110, 115, 101, 114, 116, 73, 100, 120, 73, 102, 73, 110, 66, 111, 117, 110, 100, 115,
        0,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value)
            as *mut crate::leanh::LeanObject,
        737450741554540126 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 101, 116, 73, 102, 73, 110, 66, 111, 117, 110, 100, 115, 0,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
            as *mut crate::leanh::LeanObject,
        14350272335116742732 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value:
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
    m_data: [101, 120, 116, 114, 97, 99, 116, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
            as *mut crate::leanh::LeanObject,
        8050958516035322399 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
            as *mut crate::leanh::LeanObject,
        4957202763588502154 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value:
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
    m_data: [105, 110, 115, 101, 114, 116, 73, 100, 120, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
            as *mut crate::leanh::LeanObject,
        3630988818933640571 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 101, 116, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
            as *mut crate::leanh::LeanObject,
        6372375211616468373 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
            as *mut crate::leanh::LeanObject,
        658061322716625603 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
            as *mut crate::leanh::LeanObject,
        3883600285600967666 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
            as *mut crate::leanh::LeanObject,
        4767221380455929548 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
            as *mut crate::leanh::LeanObject,
        4628900765690287007 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value:
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
    m_data: [115, 119, 97, 112, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
            as *mut crate::leanh::LeanObject,
        2036269554361060417 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
            as *mut crate::leanh::LeanObject,
        1024280003738481991 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value:
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
    m_data: [117, 115, 101, 116, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value)
            as *mut crate::leanh::LeanObject,
        17673153628822191198 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
            as *mut crate::leanh::LeanObject,
        3144473122610617097 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
            as *mut crate::leanh::LeanObject,
        16801329853220961729 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
            as *mut crate::leanh::LeanObject,
        15138447177923935175 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
            as *mut crate::leanh::LeanObject,
        16742334573394357385 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [71, 101, 116, 69, 108, 101, 109, 63, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 101, 116, 69, 108, 101, 109, 63, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value)
            as *mut crate::leanh::LeanObject,
        1284173141442213452 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value)
            as *mut crate::leanh::LeanObject,
        14790288273250445109 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value:
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
    m_data: [71, 101, 116, 69, 108, 101, 109, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value:
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
    m_data: [103, 101, 116, 69, 108, 101, 109, 0],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value)
            as *mut crate::leanh::LeanObject,
        854136310249810287 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value)
            as *mut crate::leanh::LeanObject,
        8801718159307809986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_List_numericalIndices___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_List_numericalIndices___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_List_numericalIndices___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_List_numericalIndices___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__2_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_List_numericalIndices___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalIndices___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17402736243434278163 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10154756713319201683 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7114987585215218527 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value:
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
    m_data: [114, 97, 110, 103, 101, 39, 0],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
        7934366685309624176 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
        10856004936568328432 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3800766237690652964 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value:
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
    m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 0],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2228683986675333841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        15402697716333298155 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        2966064990585596011 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        634820988191375095 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_List_numericalWidths___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_List_numericalWidths___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_numericalWidths___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_List_numericalWidths___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_numericalWidths___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value:
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
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Linter_List_bitVecWidths___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5394957827732845164 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_bitVecWidths___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_bitVecWidths___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_bitVecWidths___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 129, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 130, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 131, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 132, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_List_allowedIndices___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [105, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [106, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [107, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 116, 97, 114, 116, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__4_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 116, 111, 112, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 116, 101, 112, 0],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedIndices: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [110, 0],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [109, 0],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [108, 0],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 105, 122, 101, 0],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedWidths___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedWidths: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedBitVecWidths___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [119, 0],
};
static mut l_Lean_Linter_List_allowedBitVecWidths___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedBitVecWidths___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedBitVecWidths___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedBitVecWidths: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value:
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
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value:
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
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 119, 105, 100, 116, 104, 58, 32, 117, 115, 101, 32, 96, 110, 96, 32, 111, 114, 32, 96, 109, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 66, 105, 116, 86, 101, 99, 32, 119, 105, 100, 116, 104, 58, 32, 117, 115, 101, 32, 96, 119, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 58, 32, 117, 115, 101, 32, 96, 105, 96, 44, 32, 96, 106, 96, 44, 32, 111, 114, 32, 96, 107, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_indexLinter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_indexLinter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_indexLinter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 100, 101, 120, 76, 105, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Linter_List_indexLinter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13480916849937425914 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_indexLinter___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__2_value)
                as *mut crate::leanh::LeanObject,
            6834480939803322061 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_indexLinter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_indexLinter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_indexLinter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [114, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__1_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__2_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [116, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__3_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [116, 108, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__4_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [119, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__5_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [120, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__6_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [121, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__7_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [122, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__8_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [97, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__9_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [98, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__10_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [99, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__11_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [100, 115, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__12_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 99, 99, 0],
};
static mut l_Lean_Linter_List_allowedListNames___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__12_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__17_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__18_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__19_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__20_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__21_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__22_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__23_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__25_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__26_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedListNames: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedArrayNames: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_allowedVectorNames: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_binders___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [85, 110, 105, 116, 0],
};
static mut l_Lean_Linter_List_binders___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_binders___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9833841078580172006 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_List_binders___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_List_binders___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_List_binders___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 65, 114, 114, 97, 121, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 115, 115, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 76, 105, 115, 116, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [76, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 86, 101, 99, 116, 111, 114, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_List_listVariablesLinter___closed__0_value:
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
    m_fun: l_Lean_Linter_List_listVariablesLinter___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_List_listVariablesLinter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_listVariablesLinter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__2_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 105, 115, 116, 86, 97, 114, 105, 97, 98, 108, 101, 115, 76, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_List_listVariablesLinter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13480916849937425914 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_List_listVariablesLinter___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14015206877912852658 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_listVariablesLinter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_List_listVariablesLinter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_List_listVariablesLinter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(
    mut v_name_3239_: *mut crate::leanh::LeanObject,
    mut v_decl_3240_: *mut crate::leanh::LeanObject,
    mut v_ref_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_unused_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3243_ = crate::leanh::lean_ctor_get(v_decl_3240_, 0);
                v_descr_3244_ = crate::leanh::lean_ctor_get(v_decl_3240_, 1);
                v_deprecation_x3f_3245_ = crate::leanh::lean_ctor_get(v_decl_3240_, 2);
                v___x_3246_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3247_ = (crate::leanh::lean_unbox(v_defValue_3243_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3246_, 0 as u32, v___x_3247_);
                crate::leanh::lean_inc(v_deprecation_x3f_3245_);
                crate::leanh::lean_inc_ref(v_descr_3244_);
                crate::leanh::lean_inc_n(v_name_3239_, 2);
                v___x_3248_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3248_, 0, v_name_3239_);
                crate::leanh::lean_ctor_set(v___x_3248_, 1, v_ref_3241_);
                crate::leanh::lean_ctor_set(v___x_3248_, 2, v___x_3246_);
                crate::leanh::lean_ctor_set(v___x_3248_, 3, v_descr_3244_);
                crate::leanh::lean_ctor_set(v___x_3248_, 4, v_deprecation_x3f_3245_);
                v___x_3249_ = lean_register_option(v_name_3239_, v___x_3248_);
                if crate::leanh::lean_obj_tag(v___x_3249_) == 0 {
                    v_isSharedCheck_3257_ = (!crate::leanh::lean_is_exclusive(v___x_3249_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v_unused_3258_ = crate::leanh::lean_ctor_get(v___x_3249_, 0);
                        crate::leanh::lean_dec(v_unused_3258_);
                        v___x_3251_ = v___x_3249_;
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3249_);
                        v___x_3251_ = crate::leanh::lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3239_);
                    v_a_3259_ = crate::leanh::lean_ctor_get(v___x_3249_, 0);
                    v_isSharedCheck_3266_ = (!crate::leanh::lean_is_exclusive(v___x_3249_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3261_ = v___x_3249_;
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3259_);
                        crate::leanh::lean_dec(v___x_3249_);
                        v___x_3261_ = crate::leanh::lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3243_);
                v___x_3253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3253_, 0, v_name_3239_);
                crate::leanh::lean_ctor_set(v___x_3253_, 1, v_defValue_3243_);
                if v_isShared_3252_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3251_, 0, v___x_3253_);
                    v___x_3255_ = v___x_3251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
                    v___x_3255_ = v_reuseFailAlloc_3256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3255_;
            }
            3 => {
                if v_isShared_3262_ == 0 {
                    v___x_3264_ = v___x_3261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
                    v___x_3264_ = v_reuseFailAlloc_3265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3267_: *mut crate::leanh::LeanObject,
    mut v_decl_3268_: *mut crate::leanh::LeanObject,
    mut v_ref_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3271_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v_name_3267_, v_decl_3268_, v_ref_3269_);
    crate::leanh::lean_dec_ref(v_decl_3268_);
    return v_res_3271_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3293_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3294_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3295_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3296_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_3293_, v___x_3294_, v___x_3295_);
    return v___x_3296_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4____boxed(
    mut v_a_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
    return v_res_3298_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3316_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3317_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3318_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3319_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_3316_, v___x_3317_, v___x_3318_);
    return v___x_3319_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4____boxed(
    mut v_a_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
    return v_res_3321_;
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__0(
    mut v_i_3322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = crate::leanh::lean_box(0);
    v___x_3324_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3324_, 0, v_i_3322_);
    crate::leanh::lean_ctor_set(v___x_3324_, 1, v___x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__1(
    mut v_i_3325_: *mut crate::leanh::LeanObject,
    mut v_j_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = crate::leanh::lean_box(0);
    v___x_3328_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3328_, 0, v_j_3326_);
    crate::leanh::lean_ctor_set(v___x_3328_, 1, v___x_3327_);
    v___x_3329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3329_, 0, v_i_3325_);
    crate::leanh::lean_ctor_set(v___x_3329_, 1, v___x_3328_);
    return v___x_3329_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
    mut v_i_3330_: *mut crate::leanh::LeanObject,
    mut v_stx_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v_fvarId_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3332_) == 0 {
                    crate::leanh::lean_dec(v_stx_3331_);
                    crate::leanh::lean_dec_ref(v_i_3330_);
                    v___x_3334_ = lean_array_to_list(v_a_3333_);
                    return v___x_3334_;
                } else {
                    v_head_3335_ = crate::leanh::lean_ctor_get(v_a_3332_, 0);
                    if crate::leanh::lean_obj_tag(v_head_3335_) == 1 {
                        crate::leanh::lean_inc_ref(v_head_3335_);
                        v_tail_3336_ = crate::leanh::lean_ctor_get(v_a_3332_, 1);
                        v_isSharedCheck_3351_ = (!crate::leanh::lean_is_exclusive(v_a_3332_)) as u8;
                        if v_isSharedCheck_3351_ == 0 {
                            v_unused_3352_ = crate::leanh::lean_ctor_get(v_a_3332_, 0);
                            crate::leanh::lean_dec(v_unused_3352_);
                            v___x_3338_ = v_a_3332_;
                            v_isShared_3339_ = v_isSharedCheck_3351_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_3336_);
                            crate::leanh::lean_dec(v_a_3332_);
                            v___x_3338_ = crate::leanh::lean_box(0);
                            v_isShared_3339_ = v_isSharedCheck_3351_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_3353_ = crate::leanh::lean_ctor_get(v_a_3332_, 1);
                        crate::leanh::lean_inc(v_tail_3353_);
                        crate::leanh::lean_dec_ref_known(v_a_3332_, 2);
                        v_a_3332_ = v_tail_3353_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_3340_ = crate::leanh::lean_ctor_get(v_head_3335_, 0);
                crate::leanh::lean_inc(v_fvarId_3340_);
                crate::leanh::lean_dec_ref_known(v_head_3335_, 1);
                v_lctx_3341_ = crate::leanh::lean_ctor_get(v_i_3330_, 1);
                crate::leanh::lean_inc_ref(v_lctx_3341_);
                v___x_3342_ = lean_local_ctx_find(v_lctx_3341_, v_fvarId_3340_);
                if crate::leanh::lean_obj_tag(v___x_3342_) == 0 {
                    crate::leanh::lean_del_object(v___x_3338_);
                    v_a_3332_ = v_tail_3336_;
                    state = 0;
                    continue;
                } else {
                    v_val_3344_ = crate::leanh::lean_ctor_get(v___x_3342_, 0);
                    crate::leanh::lean_inc(v_val_3344_);
                    crate::leanh::lean_dec_ref_known(v___x_3342_, 1);
                    v___x_3345_ = l_Lean_LocalDecl_userName(v_val_3344_);
                    crate::leanh::lean_dec(v_val_3344_);
                    crate::leanh::lean_inc(v_stx_3331_);
                    if v_isShared_3339_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3338_, 0);
                        crate::leanh::lean_ctor_set(v___x_3338_, 1, v___x_3345_);
                        crate::leanh::lean_ctor_set(v___x_3338_, 0, v_stx_3331_);
                        v___x_3347_ = v___x_3338_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_stx_3331_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3345_);
                        v___x_3347_ = v_reuseFailAlloc_3350_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3348_ = lean_array_push(v_a_3333_, v___x_3347_);
                v_a_3332_ = v_tail_3336_;
                v_a_3333_ = v___x_3348_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__2(
    mut v___f_3490_: *mut crate::leanh::LeanObject,
    mut v___f_3491_: *mut crate::leanh::LeanObject,
    mut v_x_3492_: *mut crate::leanh::LeanObject,
    mut v_info_3493_: *mut crate::leanh::LeanObject,
    mut v_x_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v___y_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: u8 = 0;
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: u8 = 0;
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: u8 = 0;
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_unused_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_3493_) == 1 {
                    v_i_3495_ = crate::leanh::lean_ctor_get(v_info_3493_, 0);
                    crate::leanh::lean_inc_ref(v_i_3495_);
                    v_expr_3496_ = crate::leanh::lean_ctor_get(v_i_3495_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3496_);
                    v___x_3497_ = l_Lean_Expr_cleanupAnnotations(v_expr_3496_);
                    v___x_3498_ = l_Lean_Expr_isApp(v___x_3497_);
                    if v___x_3498_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3497_);
                        crate::leanh::lean_dec_ref_known(v_info_3493_, 1);
                        crate::leanh::lean_dec_ref(v_i_3495_);
                        crate::leanh::lean_dec_ref(v___f_3491_);
                        crate::leanh::lean_dec_ref(v___f_3490_);
                        v___x_3499_ = crate::leanh::lean_box(0);
                        return v___x_3499_;
                    } else {
                        v_arg_3500_ = crate::leanh::lean_ctor_get(v___x_3497_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3500_);
                        v___x_3501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3497_);
                        v___x_3502_ = l_Lean_Expr_isApp(v___x_3501_);
                        if v___x_3502_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3501_);
                            crate::leanh::lean_dec_ref(v_arg_3500_);
                            crate::leanh::lean_dec_ref_known(v_info_3493_, 1);
                            crate::leanh::lean_dec_ref(v_i_3495_);
                            crate::leanh::lean_dec_ref(v___f_3491_);
                            crate::leanh::lean_dec_ref(v___f_3490_);
                            v___x_3503_ = crate::leanh::lean_box(0);
                            return v___x_3503_;
                        } else {
                            v_arg_3504_ = crate::leanh::lean_ctor_get(v___x_3501_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3504_);
                            v___x_3505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3501_);
                            v___x_3506_ = l_Lean_Expr_isApp(v___x_3505_);
                            if v___x_3506_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3505_);
                                crate::leanh::lean_dec_ref(v_arg_3504_);
                                crate::leanh::lean_dec_ref(v_arg_3500_);
                                crate::leanh::lean_dec_ref_known(v_info_3493_, 1);
                                crate::leanh::lean_dec_ref(v_i_3495_);
                                crate::leanh::lean_dec_ref(v___f_3491_);
                                crate::leanh::lean_dec_ref(v___f_3490_);
                                v___x_3507_ = crate::leanh::lean_box(0);
                                return v___x_3507_;
                            } else {
                                v_arg_3508_ = crate::leanh::lean_ctor_get(v___x_3505_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3508_);
                                v_stx_3509_ = l_Lean_Elab_Info_stx(v_info_3493_);
                                v_isSharedCheck_3649_ =
                                    (!crate::leanh::lean_is_exclusive(v_info_3493_)) as u8;
                                if v_isSharedCheck_3649_ == 0 {
                                    v_unused_3650_ = crate::leanh::lean_ctor_get(v_info_3493_, 0);
                                    crate::leanh::lean_dec(v_unused_3650_);
                                    v___x_3511_ = v_info_3493_;
                                    v_isShared_3512_ = v_isSharedCheck_3649_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_info_3493_);
                                    v___x_3511_ = crate::leanh::lean_box(0);
                                    v_isShared_3512_ = v_isSharedCheck_3649_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_3493_);
                    crate::leanh::lean_dec_ref(v___f_3491_);
                    crate::leanh::lean_dec_ref(v___f_3490_);
                    v___x_3651_ = crate::leanh::lean_box(0);
                    return v___x_3651_;
                }
            }
            1 => {
                v___x_3521_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3505_);
                v___x_3522_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__3;
                v___x_3523_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3522_);
                if v___x_3523_ == 0 {
                    v___x_3524_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__5;
                    v___x_3525_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3524_);
                    if v___x_3525_ == 0 {
                        v___x_3526_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__7;
                        v___x_3527_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3526_);
                        if v___x_3527_ == 0 {
                            v___x_3528_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__9;
                            v___x_3529_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3528_);
                            if v___x_3529_ == 0 {
                                v___x_3530_ =
                                    l_Lean_Linter_List_numericalIndices___lam__2___closed__11;
                                v___x_3531_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3530_);
                                if v___x_3531_ == 0 {
                                    v___x_3532_ =
                                        l_Lean_Linter_List_numericalIndices___lam__2___closed__12;
                                    v___x_3533_ = l_Lean_Expr_isConstOf(v___x_3521_, v___x_3532_);
                                    if v___x_3533_ == 0 {
                                        v___x_3534_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__14;
                                        v___x_3535_ =
                                            l_Lean_Expr_isConstOf(v___x_3521_, v___x_3534_);
                                        if v___x_3535_ == 0 {
                                            v___x_3536_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__15;
                                            v___x_3537_ =
                                                l_Lean_Expr_isConstOf(v___x_3521_, v___x_3536_);
                                            if v___x_3537_ == 0 {
                                                v___x_3538_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__16;
                                                v___x_3539_ =
                                                    l_Lean_Expr_isConstOf(v___x_3521_, v___x_3538_);
                                                if v___x_3539_ == 0 {
                                                    v___x_3540_ = l_Lean_Expr_isApp(v___x_3521_);
                                                    if v___x_3540_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_3521_);
                                                        crate::leanh::lean_del_object(v___x_3511_);
                                                        crate::leanh::lean_dec(v_stx_3509_);
                                                        crate::leanh::lean_dec_ref(v_arg_3508_);
                                                        crate::leanh::lean_dec_ref(v_arg_3504_);
                                                        crate::leanh::lean_dec_ref(v_arg_3500_);
                                                        crate::leanh::lean_dec_ref(v_i_3495_);
                                                        crate::leanh::lean_dec_ref(v___f_3491_);
                                                        crate::leanh::lean_dec_ref(v___f_3490_);
                                                        v___x_3541_ = crate::leanh::lean_box(0);
                                                        return v___x_3541_;
                                                    } else {
                                                        v___x_3542_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_3521_,
                                                            );
                                                        v___x_3543_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__18;
                                                        v___x_3544_ = l_Lean_Expr_isConstOf(
                                                            v___x_3542_,
                                                            v___x_3543_,
                                                        );
                                                        if v___x_3544_ == 0 {
                                                            v___x_3545_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__19;
                                                            v___x_3546_ = l_Lean_Expr_isConstOf(
                                                                v___x_3542_,
                                                                v___x_3545_,
                                                            );
                                                            if v___x_3546_ == 0 {
                                                                v___x_3547_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__20;
                                                                v___x_3548_ = l_Lean_Expr_isConstOf(
                                                                    v___x_3542_,
                                                                    v___x_3547_,
                                                                );
                                                                if v___x_3548_ == 0 {
                                                                    v___x_3549_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__21;
                                                                    v___x_3550_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_3542_,
                                                                            v___x_3549_,
                                                                        );
                                                                    if v___x_3550_ == 0 {
                                                                        v___x_3551_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__22;
                                                                        v___x_3552_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_3542_,
                                                                                v___x_3551_,
                                                                            );
                                                                        if v___x_3552_ == 0 {
                                                                            v___x_3553_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__24;
                                                                            v___x_3554_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3553_);
                                                                            if v___x_3554_ == 0 {
                                                                                v___x_3555_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__26;
                                                                                v___x_3556_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3555_);
                                                                                if v___x_3556_ == 0
                                                                                {
                                                                                    v___x_3557_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__27;
                                                                                    v___x_3558_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3557_);
                                                                                    if v___x_3558_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_3559_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__29;
                                                                                        v___x_3560_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3559_);
                                                                                        if v___x_3560_ == 0 {
v___x_3561_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__31;
v___x_3562_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3561_);
if v___x_3562_ == 0 {
v___x_3563_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__33;
v___x_3564_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3563_);
if v___x_3564_ == 0 {
v___x_3565_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__35;
v___x_3566_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3565_);
if v___x_3566_ == 0 {
v___x_3567_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__36;
v___x_3568_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3567_);
if v___x_3568_ == 0 {
v___x_3569_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__38;
v___x_3570_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3569_);
if v___x_3570_ == 0 {
v___x_3571_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__40;
v___x_3572_ = l_Lean_Expr_isConstOf(v___x_3542_, v___x_3571_);
if v___x_3572_ == 0 {
v___x_3573_ = l_Lean_Expr_isApp(v___x_3542_);
if v___x_3573_ == 0 {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_del_object(v___x_3511_);
crate::leanh::lean_dec(v_stx_3509_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v_i_3495_);
crate::leanh::lean_dec_ref(v___f_3491_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3574_ = crate::leanh::lean_box(0);
return v___x_3574_;
} else {
v___x_3575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3542_);
v___x_3576_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__41;
v___x_3577_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3576_);
if v___x_3577_ == 0 {
v___x_3578_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__42;
v___x_3579_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3578_);
if v___x_3579_ == 0 {
v___x_3580_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__43;
v___x_3581_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3580_);
if v___x_3581_ == 0 {
v___x_3582_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__44;
v___x_3583_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3582_);
if v___x_3583_ == 0 {
v___x_3584_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__46;
v___x_3585_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3584_);
if v___x_3585_ == 0 {
v___x_3586_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__47;
v___x_3587_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3586_);
if v___x_3587_ == 0 {
v___x_3588_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__49;
v___x_3589_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3588_);
if v___x_3589_ == 0 {
v___x_3590_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__50;
v___x_3591_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3590_);
if v___x_3591_ == 0 {
v___x_3592_ = l_Lean_Expr_isApp(v___x_3575_);
if v___x_3592_ == 0 {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_del_object(v___x_3511_);
crate::leanh::lean_dec(v_stx_3509_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v_i_3495_);
crate::leanh::lean_dec_ref(v___f_3491_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3593_ = crate::leanh::lean_box(0);
return v___x_3593_;
} else {
v___x_3594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3575_);
v___x_3595_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__51;
v___x_3596_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3595_);
if v___x_3596_ == 0 {
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3597_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__52;
v___x_3598_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3597_);
if v___x_3598_ == 0 {
v___x_3599_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__53;
v___x_3600_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3599_);
if v___x_3600_ == 0 {
crate::leanh::lean_dec_ref(v_arg_3508_);
v___x_3601_ = l_Lean_Expr_isApp(v___x_3594_);
if v___x_3601_ == 0 {
crate::leanh::lean_dec_ref(v___x_3594_);
crate::leanh::lean_del_object(v___x_3511_);
crate::leanh::lean_dec(v_stx_3509_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v_i_3495_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3602_ = crate::leanh::lean_box(0);
return v___x_3602_;
} else {
v___x_3603_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3594_);
v___x_3604_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__56;
v___x_3605_ = l_Lean_Expr_isConstOf(v___x_3603_, v___x_3604_);
if v___x_3605_ == 0 {
crate::leanh::lean_dec_ref(v_arg_3500_);
v___x_3606_ = l_Lean_Expr_isApp(v___x_3603_);
if v___x_3606_ == 0 {
crate::leanh::lean_dec_ref(v___x_3603_);
crate::leanh::lean_del_object(v___x_3511_);
crate::leanh::lean_dec(v_stx_3509_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_i_3495_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3607_ = crate::leanh::lean_box(0);
return v___x_3607_;
} else {
v___x_3608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3603_);
v___x_3609_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__59;
v___x_3610_ = l_Lean_Expr_isConstOf(v___x_3608_, v___x_3609_);
crate::leanh::lean_dec_ref(v___x_3608_);
if v___x_3610_ == 0 {
crate::leanh::lean_del_object(v___x_3511_);
crate::leanh::lean_dec(v_stx_3509_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_i_3495_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3611_ = crate::leanh::lean_box(0);
return v___x_3611_;
} else {
v___x_3612_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3612_;
state = 2; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v___x_3603_);
crate::leanh::lean_dec_ref(v_arg_3504_);
v___x_3613_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
v___y_3514_ = v___x_3613_;
state = 2; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v___x_3594_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
v___x_3614_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3614_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3594_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
v___x_3615_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3615_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3594_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3616_ = crate::leanh::lean_apply_2(v___f_3491_, v_arg_3508_, v_arg_3504_);
v___y_3514_ = v___x_3616_;
state = 2; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3617_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3617_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3618_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3618_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3504_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3619_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3619_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3620_ = crate::leanh::lean_apply_2(v___f_3491_, v_arg_3508_, v_arg_3504_);
v___y_3514_ = v___x_3620_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3621_ = crate::leanh::lean_apply_2(v___f_3491_, v_arg_3504_, v_arg_3500_);
v___y_3514_ = v___x_3621_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3622_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3622_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3623_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3623_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3575_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3624_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3624_;
state = 2; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3625_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3625_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3626_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3626_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3627_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3627_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v___f_3490_);
v___x_3628_ = crate::leanh::lean_apply_2(v___f_3491_, v_arg_3504_, v_arg_3500_);
v___y_3514_ = v___x_3628_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3629_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3629_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3630_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3630_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v___x_3542_);
crate::leanh::lean_dec_ref(v_arg_3508_);
crate::leanh::lean_dec_ref(v_arg_3500_);
crate::leanh::lean_dec_ref(v___f_3491_);
v___x_3631_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3631_;
state = 2; continue;
}
                                                                                    } else {
                                                                                        crate::leanh::lean_dec_ref(v___x_3542_);
                                                                                        crate::leanh::lean_dec_ref(v_arg_3508_);
                                                                                        crate::leanh::lean_dec_ref(v_arg_3500_);
                                                                                        crate::leanh::lean_dec_ref(v___f_3491_);
                                                                                        v___x_3632_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
                                                                                        v___y_3514_ = v___x_3632_;
                                                                                        state = 2;
                                                                                        continue;
                                                                                    }
                                                                                } else {
                                                                                    crate::leanh::lean_dec_ref(v___x_3542_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_3508_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_3500_);
                                                                                    crate::leanh::lean_dec_ref(v___f_3491_);
                                                                                    v___x_3633_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
                                                                                    v___y_3514_ =
                                                                                        v___x_3633_;
                                                                                    state = 2;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                crate::leanh::lean_dec_ref(v___x_3542_);
                                                                                crate::leanh::lean_dec_ref(v_arg_3508_);
                                                                                crate::leanh::lean_dec_ref(v_arg_3500_);
                                                                                crate::leanh::lean_dec_ref(v___f_3491_);
                                                                                v___x_3634_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3504_);
                                                                                v___y_3514_ =
                                                                                    v___x_3634_;
                                                                                state = 2;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v___x_3542_);
                                                                            crate::leanh::lean_dec_ref(v_arg_3508_);
                                                                            crate::leanh::lean_dec_ref(v_arg_3504_);
                                                                            crate::leanh::lean_dec_ref(v___f_3491_);
                                                                            v___x_3635_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                                                                            v___y_3514_ =
                                                                                v___x_3635_;
                                                                            state = 2;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_3542_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3508_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3504_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___f_3491_,
                                                                        );
                                                                        v___x_3636_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                                                                        v___y_3514_ = v___x_3636_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_3542_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3508_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3504_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___f_3491_,
                                                                    );
                                                                    v___x_3637_ =
                                                                        crate::leanh::lean_apply_1(
                                                                            v___f_3490_,
                                                                            v_arg_3500_,
                                                                        );
                                                                    v___y_3514_ = v___x_3637_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3542_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3508_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3504_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___f_3491_,
                                                                );
                                                                v___x_3638_ =
                                                                    crate::leanh::lean_apply_1(
                                                                        v___f_3490_,
                                                                        v_arg_3500_,
                                                                    );
                                                                v___y_3514_ = v___x_3638_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_3542_);
                                                            crate::leanh::lean_dec_ref(v_arg_3508_);
                                                            crate::leanh::lean_dec_ref(v_arg_3504_);
                                                            crate::leanh::lean_dec_ref(v___f_3491_);
                                                            v___x_3639_ =
                                                                crate::leanh::lean_apply_1(
                                                                    v___f_3490_,
                                                                    v_arg_3500_,
                                                                );
                                                            v___y_3514_ = v___x_3639_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3521_);
                                                    crate::leanh::lean_dec_ref(v_arg_3508_);
                                                    crate::leanh::lean_dec_ref(v_arg_3500_);
                                                    crate::leanh::lean_dec_ref(v___f_3491_);
                                                    v___x_3640_ = crate::leanh::lean_apply_1(
                                                        v___f_3490_,
                                                        v_arg_3504_,
                                                    );
                                                    v___y_3514_ = v___x_3640_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3521_);
                                                crate::leanh::lean_dec_ref(v_arg_3508_);
                                                crate::leanh::lean_dec_ref(v_arg_3500_);
                                                crate::leanh::lean_dec_ref(v___f_3491_);
                                                v___x_3641_ = crate::leanh::lean_apply_1(
                                                    v___f_3490_,
                                                    v_arg_3504_,
                                                );
                                                v___y_3514_ = v___x_3641_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3521_);
                                            crate::leanh::lean_dec_ref(v_arg_3508_);
                                            crate::leanh::lean_dec_ref(v_arg_3504_);
                                            crate::leanh::lean_dec_ref(v___f_3491_);
                                            v___x_3642_ = crate::leanh::lean_apply_1(
                                                v___f_3490_,
                                                v_arg_3500_,
                                            );
                                            v___y_3514_ = v___x_3642_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_3521_);
                                        crate::leanh::lean_dec_ref(v_arg_3508_);
                                        crate::leanh::lean_dec_ref(v_arg_3504_);
                                        crate::leanh::lean_dec_ref(v___f_3491_);
                                        v___x_3643_ =
                                            crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                                        v___y_3514_ = v___x_3643_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3521_);
                                    crate::leanh::lean_dec_ref(v_arg_3508_);
                                    crate::leanh::lean_dec_ref(v_arg_3504_);
                                    crate::leanh::lean_dec_ref(v___f_3491_);
                                    v___x_3644_ =
                                        crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                                    v___y_3514_ = v___x_3644_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3521_);
                                crate::leanh::lean_dec_ref(v_arg_3508_);
                                crate::leanh::lean_dec_ref(v_arg_3504_);
                                crate::leanh::lean_dec_ref(v___f_3491_);
                                v___x_3645_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                                v___y_3514_ = v___x_3645_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3521_);
                            crate::leanh::lean_dec_ref(v_arg_3508_);
                            crate::leanh::lean_dec_ref(v_arg_3504_);
                            crate::leanh::lean_dec_ref(v___f_3491_);
                            v___x_3646_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                            v___y_3514_ = v___x_3646_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3521_);
                        crate::leanh::lean_dec_ref(v_arg_3508_);
                        crate::leanh::lean_dec_ref(v_arg_3504_);
                        crate::leanh::lean_dec_ref(v___f_3491_);
                        v___x_3647_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                        v___y_3514_ = v___x_3647_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3521_);
                    crate::leanh::lean_dec_ref(v_arg_3508_);
                    crate::leanh::lean_dec_ref(v_arg_3504_);
                    crate::leanh::lean_dec_ref(v___f_3491_);
                    v___x_3648_ = crate::leanh::lean_apply_1(v___f_3490_, v_arg_3500_);
                    v___y_3514_ = v___x_3648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3514_) == 0 {
                    crate::leanh::lean_del_object(v___x_3511_);
                    crate::leanh::lean_dec(v_stx_3509_);
                    crate::leanh::lean_dec_ref(v_i_3495_);
                    v___x_3515_ = crate::leanh::lean_box(0);
                    return v___x_3515_;
                } else {
                    v___x_3516_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
                    v___x_3517_ =
                        l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
                            v_i_3495_,
                            v_stx_3509_,
                            v___y_3514_,
                            v___x_3516_,
                        );
                    if v_isShared_3512_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3511_, 0, v___x_3517_);
                        v___x_3519_ = v___x_3511_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
                        v___x_3519_ = v_reuseFailAlloc_3520_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__2___boxed(
    mut v___f_3652_: *mut crate::leanh::LeanObject,
    mut v___f_3653_: *mut crate::leanh::LeanObject,
    mut v_x_3654_: *mut crate::leanh::LeanObject,
    mut v_info_3655_: *mut crate::leanh::LeanObject,
    mut v_x_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_Linter_List_numericalIndices___lam__2(
        v___f_3652_,
        v___f_3653_,
        v_x_3654_,
        v_info_3655_,
        v_x_3656_,
    );
    crate::leanh::lean_dec_ref(v_x_3656_);
    crate::leanh::lean_dec_ref(v_x_3654_);
    return v_res_3657_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(
    mut v_a_3658_: *mut crate::leanh::LeanObject,
    mut v_a_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3658_) == 0 {
                    v___x_3660_ = lean_array_to_list(v_a_3659_);
                    return v___x_3660_;
                } else {
                    v_head_3661_ = crate::leanh::lean_ctor_get(v_a_3658_, 0);
                    crate::leanh::lean_inc(v_head_3661_);
                    v_tail_3662_ = crate::leanh::lean_ctor_get(v_a_3658_, 1);
                    crate::leanh::lean_inc(v_tail_3662_);
                    crate::leanh::lean_dec_ref_known(v_a_3658_, 2);
                    v___x_3663_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3659_,
                        v_head_3661_,
                    );
                    v_a_3658_ = v_tail_3662_;
                    v_a_3659_ = v___x_3663_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_numericalIndices(
    mut v_t_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3671_ = l_Lean_Linter_List_numericalIndices___closed__2;
    v___x_3672_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3671_, v_t_3670_);
    v___x_3673_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3674_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3672_, v___x_3673_);
    return v___x_3674_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths___lam__0(
    mut v_n_3675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ = crate::leanh::lean_box(0);
    v___x_3677_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3677_, 0, v_n_3675_);
    crate::leanh::lean_ctor_set(v___x_3677_, 1, v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths___lam__1(
    mut v___f_3710_: *mut crate::leanh::LeanObject,
    mut v_x_3711_: *mut crate::leanh::LeanObject,
    mut v_info_3712_: *mut crate::leanh::LeanObject,
    mut v_x_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___y_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_unused_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_3712_) == 1 {
                    v_i_3714_ = crate::leanh::lean_ctor_get(v_info_3712_, 0);
                    crate::leanh::lean_inc_ref(v_i_3714_);
                    v_expr_3715_ = crate::leanh::lean_ctor_get(v_i_3714_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3715_);
                    v___x_3716_ = l_Lean_Expr_cleanupAnnotations(v_expr_3715_);
                    v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
                    if v___x_3717_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3716_);
                        crate::leanh::lean_dec_ref(v_i_3714_);
                        crate::leanh::lean_dec_ref_known(v_info_3712_, 1);
                        crate::leanh::lean_dec_ref(v___f_3710_);
                        v___x_3718_ = crate::leanh::lean_box(0);
                        return v___x_3718_;
                    } else {
                        v_arg_3719_ = crate::leanh::lean_ctor_get(v___x_3716_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3719_);
                        v_stx_3720_ = l_Lean_Elab_Info_stx(v_info_3712_);
                        v_isSharedCheck_3771_ =
                            (!crate::leanh::lean_is_exclusive(v_info_3712_)) as u8;
                        if v_isSharedCheck_3771_ == 0 {
                            v_unused_3772_ = crate::leanh::lean_ctor_get(v_info_3712_, 0);
                            crate::leanh::lean_dec(v_unused_3772_);
                            v___x_3722_ = v_info_3712_;
                            v_isShared_3723_ = v_isSharedCheck_3771_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_info_3712_);
                            v___x_3722_ = crate::leanh::lean_box(0);
                            v_isShared_3723_ = v_isSharedCheck_3771_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_3712_);
                    crate::leanh::lean_dec_ref(v___f_3710_);
                    v___x_3773_ = crate::leanh::lean_box(0);
                    return v___x_3773_;
                }
            }
            1 => {
                v___x_3732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3716_);
                v___x_3733_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__1;
                v___x_3734_ = l_Lean_Expr_isConstOf(v___x_3732_, v___x_3733_);
                if v___x_3734_ == 0 {
                    v___x_3735_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__2;
                    v___x_3736_ = l_Lean_Expr_isConstOf(v___x_3732_, v___x_3735_);
                    if v___x_3736_ == 0 {
                        v___x_3737_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__3;
                        v___x_3738_ = l_Lean_Expr_isConstOf(v___x_3732_, v___x_3737_);
                        if v___x_3738_ == 0 {
                            v___x_3739_ = l_Lean_Expr_isApp(v___x_3732_);
                            if v___x_3739_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3732_);
                                crate::leanh::lean_del_object(v___x_3722_);
                                crate::leanh::lean_dec(v_stx_3720_);
                                crate::leanh::lean_dec_ref(v_arg_3719_);
                                crate::leanh::lean_dec_ref(v_i_3714_);
                                crate::leanh::lean_dec_ref(v___f_3710_);
                                v___x_3740_ = crate::leanh::lean_box(0);
                                return v___x_3740_;
                            } else {
                                v_arg_3741_ = crate::leanh::lean_ctor_get(v___x_3732_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3741_);
                                v___x_3742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3732_);
                                v___x_3743_ =
                                    l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                                v___x_3744_ = l_Lean_Expr_isConstOf(v___x_3742_, v___x_3743_);
                                if v___x_3744_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_3719_);
                                    v___x_3745_ = l_Lean_Expr_isApp(v___x_3742_);
                                    if v___x_3745_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3742_);
                                        crate::leanh::lean_dec_ref(v_arg_3741_);
                                        crate::leanh::lean_del_object(v___x_3722_);
                                        crate::leanh::lean_dec(v_stx_3720_);
                                        crate::leanh::lean_dec_ref(v_i_3714_);
                                        crate::leanh::lean_dec_ref(v___f_3710_);
                                        v___x_3746_ = crate::leanh::lean_box(0);
                                        return v___x_3746_;
                                    } else {
                                        v___x_3747_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3742_);
                                        v___x_3748_ =
                                            l_Lean_Linter_List_numericalWidths___lam__1___closed__6;
                                        v___x_3749_ =
                                            l_Lean_Expr_isConstOf(v___x_3747_, v___x_3748_);
                                        if v___x_3749_ == 0 {
                                            v___x_3750_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__7;
                                            v___x_3751_ =
                                                l_Lean_Expr_isConstOf(v___x_3747_, v___x_3750_);
                                            if v___x_3751_ == 0 {
                                                v___x_3752_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__8;
                                                v___x_3753_ =
                                                    l_Lean_Expr_isConstOf(v___x_3747_, v___x_3752_);
                                                if v___x_3753_ == 0 {
                                                    v___x_3754_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__10;
                                                    v___x_3755_ = l_Lean_Expr_isConstOf(
                                                        v___x_3747_,
                                                        v___x_3754_,
                                                    );
                                                    if v___x_3755_ == 0 {
                                                        v___x_3756_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__11;
                                                        v___x_3757_ = l_Lean_Expr_isConstOf(
                                                            v___x_3747_,
                                                            v___x_3756_,
                                                        );
                                                        if v___x_3757_ == 0 {
                                                            v___x_3758_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__12;
                                                            v___x_3759_ = l_Lean_Expr_isConstOf(
                                                                v___x_3747_,
                                                                v___x_3758_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_3747_);
                                                            if v___x_3759_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3741_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3722_,
                                                                );
                                                                crate::leanh::lean_dec(v_stx_3720_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_i_3714_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___f_3710_,
                                                                );
                                                                v___x_3760_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_3760_;
                                                            } else {
                                                                v___x_3761_ =
                                                                    crate::leanh::lean_apply_1(
                                                                        v___f_3710_,
                                                                        v_arg_3741_,
                                                                    );
                                                                v___y_3725_ = v___x_3761_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_3747_);
                                                            v___x_3762_ =
                                                                crate::leanh::lean_apply_1(
                                                                    v___f_3710_,
                                                                    v_arg_3741_,
                                                                );
                                                            v___y_3725_ = v___x_3762_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_3747_);
                                                        v___x_3763_ = crate::leanh::lean_apply_1(
                                                            v___f_3710_,
                                                            v_arg_3741_,
                                                        );
                                                        v___y_3725_ = v___x_3763_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3747_);
                                                    v___x_3764_ = crate::leanh::lean_apply_1(
                                                        v___f_3710_,
                                                        v_arg_3741_,
                                                    );
                                                    v___y_3725_ = v___x_3764_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3747_);
                                                v___x_3765_ = crate::leanh::lean_apply_1(
                                                    v___f_3710_,
                                                    v_arg_3741_,
                                                );
                                                v___y_3725_ = v___x_3765_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3747_);
                                            v___x_3766_ = crate::leanh::lean_apply_1(
                                                v___f_3710_,
                                                v_arg_3741_,
                                            );
                                            v___y_3725_ = v___x_3766_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3742_);
                                    crate::leanh::lean_dec_ref(v_arg_3741_);
                                    v___x_3767_ =
                                        crate::leanh::lean_apply_1(v___f_3710_, v_arg_3719_);
                                    v___y_3725_ = v___x_3767_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3732_);
                            v___x_3768_ = crate::leanh::lean_apply_1(v___f_3710_, v_arg_3719_);
                            v___y_3725_ = v___x_3768_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3732_);
                        v___x_3769_ = crate::leanh::lean_apply_1(v___f_3710_, v_arg_3719_);
                        v___y_3725_ = v___x_3769_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3732_);
                    v___x_3770_ = crate::leanh::lean_apply_1(v___f_3710_, v_arg_3719_);
                    v___y_3725_ = v___x_3770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3725_) == 0 {
                    crate::leanh::lean_del_object(v___x_3722_);
                    crate::leanh::lean_dec(v_stx_3720_);
                    crate::leanh::lean_dec_ref(v_i_3714_);
                    v___x_3726_ = crate::leanh::lean_box(0);
                    return v___x_3726_;
                } else {
                    v___x_3727_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
                    v___x_3728_ =
                        l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
                            v_i_3714_,
                            v_stx_3720_,
                            v___y_3725_,
                            v___x_3727_,
                        );
                    if v_isShared_3723_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3722_, 0, v___x_3728_);
                        v___x_3730_ = v___x_3722_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
                        v___x_3730_ = v_reuseFailAlloc_3731_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_numericalWidths___lam__1___boxed(
    mut v___f_3774_: *mut crate::leanh::LeanObject,
    mut v_x_3775_: *mut crate::leanh::LeanObject,
    mut v_info_3776_: *mut crate::leanh::LeanObject,
    mut v_x_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_Lean_Linter_List_numericalWidths___lam__1(
        v___f_3774_,
        v_x_3775_,
        v_info_3776_,
        v_x_3777_,
    );
    crate::leanh::lean_dec_ref(v_x_3777_);
    crate::leanh::lean_dec_ref(v_x_3775_);
    return v_res_3778_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths(
    mut v_t_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3783_ = l_Lean_Linter_List_numericalWidths___closed__1;
    v___x_3784_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3783_, v_t_3782_);
    v___x_3785_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3786_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3784_, v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Linter_List_bitVecWidths___lam__0(
    mut v_x_3790_: *mut crate::leanh::LeanObject,
    mut v_info_3791_: *mut crate::leanh::LeanObject,
    mut v_x_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_unused_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_3791_) == 1 {
                    v_i_3793_ = crate::leanh::lean_ctor_get(v_info_3791_, 0);
                    crate::leanh::lean_inc_ref(v_i_3793_);
                    v_expr_3794_ = crate::leanh::lean_ctor_get(v_i_3793_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3794_);
                    v___x_3795_ = l_Lean_Expr_cleanupAnnotations(v_expr_3794_);
                    v___x_3796_ = l_Lean_Expr_isApp(v___x_3795_);
                    if v___x_3796_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3795_);
                        crate::leanh::lean_dec_ref(v_i_3793_);
                        crate::leanh::lean_dec_ref_known(v_info_3791_, 1);
                        v___x_3797_ = crate::leanh::lean_box(0);
                        return v___x_3797_;
                    } else {
                        v_arg_3798_ = crate::leanh::lean_ctor_get(v___x_3795_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3798_);
                        v___x_3799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3795_);
                        v___x_3800_ = l_Lean_Linter_List_bitVecWidths___lam__0___closed__1;
                        v___x_3801_ = l_Lean_Expr_isConstOf(v___x_3799_, v___x_3800_);
                        crate::leanh::lean_dec_ref(v___x_3799_);
                        if v___x_3801_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_3798_);
                            crate::leanh::lean_dec_ref(v_i_3793_);
                            crate::leanh::lean_dec_ref_known(v_info_3791_, 1);
                            v___x_3802_ = crate::leanh::lean_box(0);
                            return v___x_3802_;
                        } else {
                            v_stx_3803_ = l_Lean_Elab_Info_stx(v_info_3791_);
                            v_isSharedCheck_3814_ =
                                (!crate::leanh::lean_is_exclusive(v_info_3791_)) as u8;
                            if v_isSharedCheck_3814_ == 0 {
                                v_unused_3815_ = crate::leanh::lean_ctor_get(v_info_3791_, 0);
                                crate::leanh::lean_dec(v_unused_3815_);
                                v___x_3805_ = v_info_3791_;
                                v_isShared_3806_ = v_isSharedCheck_3814_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_info_3791_);
                                v___x_3805_ = crate::leanh::lean_box(0);
                                v_isShared_3806_ = v_isSharedCheck_3814_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_3791_);
                    v___x_3816_ = crate::leanh::lean_box(0);
                    return v___x_3816_;
                }
            }
            1 => {
                v___x_3807_ = crate::leanh::lean_box(0);
                v___x_3808_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v_arg_3798_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                v___x_3809_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
                v___x_3810_ =
                    l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
                        v_i_3793_,
                        v_stx_3803_,
                        v___x_3808_,
                        v___x_3809_,
                    );
                if v_isShared_3806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3810_);
                    v___x_3812_ = v___x_3805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_bitVecWidths___lam__0___boxed(
    mut v_x_3817_: *mut crate::leanh::LeanObject,
    mut v_info_3818_: *mut crate::leanh::LeanObject,
    mut v_x_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Lean_Linter_List_bitVecWidths___lam__0(v_x_3817_, v_info_3818_, v_x_3819_);
    crate::leanh::lean_dec_ref(v_x_3819_);
    crate::leanh::lean_dec_ref(v_x_3817_);
    return v_res_3820_;
}
pub unsafe fn l_Lean_Linter_List_bitVecWidths(
    mut v_t_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3823_ = l_Lean_Linter_List_bitVecWidths___closed__0;
    v___x_3824_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3823_, v_t_3822_);
    v___x_3825_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3826_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3824_, v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0;
    v___x_3829_ = lean_string_utf8_byte_size(v___x_3828_);
    return v___x_3829_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(
    mut v_s_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_unused_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3831_ = crate::leanh::lean_ctor_get(v_s_3830_, 0);
                v_startInclusive_3832_ = crate::leanh::lean_ctor_get(v_s_3830_, 1);
                v_endExclusive_3833_ = crate::leanh::lean_ctor_get(v_s_3830_, 2);
                v___x_3834_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0;
                v___x_3835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1);
                v___x_3836_ = lean_nat_sub(v_endExclusive_3833_, v_startInclusive_3832_);
                v___x_3837_ = lean_nat_dec_le(v___x_3835_, v___x_3836_);
                if v___x_3837_ == 0 {
                    crate::leanh::lean_dec(v___x_3836_);
                    return v_s_3830_;
                } else {
                    v___x_3838_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3839_ = lean_nat_sub(v___x_3836_, v___x_3835_);
                    crate::leanh::lean_dec(v___x_3836_);
                    v___x_3840_ = lean_nat_add(v_startInclusive_3832_, v___x_3839_);
                    v___x_3841_ = lean_string_memcmp(
                        v_str_3831_,
                        v___x_3834_,
                        v___x_3840_,
                        v___x_3838_,
                        v___x_3835_,
                    );
                    crate::leanh::lean_dec(v___x_3840_);
                    if v___x_3841_ == 0 {
                        crate::leanh::lean_dec(v___x_3839_);
                        return v_s_3830_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_3832_);
                        crate::leanh::lean_inc_ref(v_str_3831_);
                        v___x_3842_ = l_String_Slice_pos_x21(v_s_3830_, v___x_3839_);
                        crate::leanh::lean_dec(v___x_3839_);
                        v_isSharedCheck_3850_ = (!crate::leanh::lean_is_exclusive(v_s_3830_)) as u8;
                        if v_isSharedCheck_3850_ == 0 {
                            v_unused_3851_ = crate::leanh::lean_ctor_get(v_s_3830_, 2);
                            crate::leanh::lean_dec(v_unused_3851_);
                            v_unused_3852_ = crate::leanh::lean_ctor_get(v_s_3830_, 1);
                            crate::leanh::lean_dec(v_unused_3852_);
                            v_unused_3853_ = crate::leanh::lean_ctor_get(v_s_3830_, 0);
                            crate::leanh::lean_dec(v_unused_3853_);
                            v___x_3844_ = v_s_3830_;
                            v_isShared_3845_ = v_isSharedCheck_3850_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_3830_);
                            v___x_3844_ = crate::leanh::lean_box(0);
                            v_isShared_3845_ = v_isSharedCheck_3850_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3846_ = lean_nat_add(v_startInclusive_3832_, v___x_3842_);
                crate::leanh::lean_dec(v___x_3842_);
                if v_isShared_3845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3844_, 2, v___x_3846_);
                    v___x_3848_ = v___x_3844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_str_3831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_startInclusive_3832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 2, v___x_3846_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0;
    v___x_3856_ = lean_string_utf8_byte_size(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(
    mut v_s_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut v_unused_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3858_ = crate::leanh::lean_ctor_get(v_s_3857_, 0);
                v_startInclusive_3859_ = crate::leanh::lean_ctor_get(v_s_3857_, 1);
                v_endExclusive_3860_ = crate::leanh::lean_ctor_get(v_s_3857_, 2);
                v___x_3861_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0;
                v___x_3862_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1);
                v___x_3863_ = lean_nat_sub(v_endExclusive_3860_, v_startInclusive_3859_);
                v___x_3864_ = lean_nat_dec_le(v___x_3862_, v___x_3863_);
                if v___x_3864_ == 0 {
                    crate::leanh::lean_dec(v___x_3863_);
                    return v_s_3857_;
                } else {
                    v___x_3865_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3866_ = lean_nat_sub(v___x_3863_, v___x_3862_);
                    crate::leanh::lean_dec(v___x_3863_);
                    v___x_3867_ = lean_nat_add(v_startInclusive_3859_, v___x_3866_);
                    v___x_3868_ = lean_string_memcmp(
                        v_str_3858_,
                        v___x_3861_,
                        v___x_3867_,
                        v___x_3865_,
                        v___x_3862_,
                    );
                    crate::leanh::lean_dec(v___x_3867_);
                    if v___x_3868_ == 0 {
                        crate::leanh::lean_dec(v___x_3866_);
                        return v_s_3857_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_3859_);
                        crate::leanh::lean_inc_ref(v_str_3858_);
                        v___x_3869_ = l_String_Slice_pos_x21(v_s_3857_, v___x_3866_);
                        crate::leanh::lean_dec(v___x_3866_);
                        v_isSharedCheck_3877_ = (!crate::leanh::lean_is_exclusive(v_s_3857_)) as u8;
                        if v_isSharedCheck_3877_ == 0 {
                            v_unused_3878_ = crate::leanh::lean_ctor_get(v_s_3857_, 2);
                            crate::leanh::lean_dec(v_unused_3878_);
                            v_unused_3879_ = crate::leanh::lean_ctor_get(v_s_3857_, 1);
                            crate::leanh::lean_dec(v_unused_3879_);
                            v_unused_3880_ = crate::leanh::lean_ctor_get(v_s_3857_, 0);
                            crate::leanh::lean_dec(v_unused_3880_);
                            v___x_3871_ = v_s_3857_;
                            v_isShared_3872_ = v_isSharedCheck_3877_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_3857_);
                            v___x_3871_ = crate::leanh::lean_box(0);
                            v_isShared_3872_ = v_isSharedCheck_3877_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3873_ = lean_nat_add(v_startInclusive_3859_, v___x_3869_);
                crate::leanh::lean_dec(v___x_3869_);
                if v_isShared_3872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3871_, 2, v___x_3873_);
                    v___x_3875_ = v___x_3871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_str_3858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_startInclusive_3859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 2, v___x_3873_);
                    v___x_3875_ = v_reuseFailAlloc_3876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0;
    v___x_3883_ = lean_string_utf8_byte_size(v___x_3882_);
    return v___x_3883_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(
    mut v_s_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v_unused_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3885_ = crate::leanh::lean_ctor_get(v_s_3884_, 0);
                v_startInclusive_3886_ = crate::leanh::lean_ctor_get(v_s_3884_, 1);
                v_endExclusive_3887_ = crate::leanh::lean_ctor_get(v_s_3884_, 2);
                v___x_3888_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0;
                v___x_3889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1);
                v___x_3890_ = lean_nat_sub(v_endExclusive_3887_, v_startInclusive_3886_);
                v___x_3891_ = lean_nat_dec_le(v___x_3889_, v___x_3890_);
                if v___x_3891_ == 0 {
                    crate::leanh::lean_dec(v___x_3890_);
                    return v_s_3884_;
                } else {
                    v___x_3892_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3893_ = lean_nat_sub(v___x_3890_, v___x_3889_);
                    crate::leanh::lean_dec(v___x_3890_);
                    v___x_3894_ = lean_nat_add(v_startInclusive_3886_, v___x_3893_);
                    v___x_3895_ = lean_string_memcmp(
                        v_str_3885_,
                        v___x_3888_,
                        v___x_3894_,
                        v___x_3892_,
                        v___x_3889_,
                    );
                    crate::leanh::lean_dec(v___x_3894_);
                    if v___x_3895_ == 0 {
                        crate::leanh::lean_dec(v___x_3893_);
                        return v_s_3884_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_3886_);
                        crate::leanh::lean_inc_ref(v_str_3885_);
                        v___x_3896_ = l_String_Slice_pos_x21(v_s_3884_, v___x_3893_);
                        crate::leanh::lean_dec(v___x_3893_);
                        v_isSharedCheck_3904_ = (!crate::leanh::lean_is_exclusive(v_s_3884_)) as u8;
                        if v_isSharedCheck_3904_ == 0 {
                            v_unused_3905_ = crate::leanh::lean_ctor_get(v_s_3884_, 2);
                            crate::leanh::lean_dec(v_unused_3905_);
                            v_unused_3906_ = crate::leanh::lean_ctor_get(v_s_3884_, 1);
                            crate::leanh::lean_dec(v_unused_3906_);
                            v_unused_3907_ = crate::leanh::lean_ctor_get(v_s_3884_, 0);
                            crate::leanh::lean_dec(v_unused_3907_);
                            v___x_3898_ = v_s_3884_;
                            v_isShared_3899_ = v_isSharedCheck_3904_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_3884_);
                            v___x_3898_ = crate::leanh::lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3904_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3900_ = lean_nat_add(v_startInclusive_3886_, v___x_3896_);
                crate::leanh::lean_dec(v___x_3896_);
                if v_isShared_3899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3898_, 2, v___x_3900_);
                    v___x_3902_ = v___x_3898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_str_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_startInclusive_3886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 2, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0;
    v___x_3910_ = lean_string_utf8_byte_size(v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(
    mut v_s_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3912_ = crate::leanh::lean_ctor_get(v_s_3911_, 0);
                v_startInclusive_3913_ = crate::leanh::lean_ctor_get(v_s_3911_, 1);
                v_endExclusive_3914_ = crate::leanh::lean_ctor_get(v_s_3911_, 2);
                v___x_3915_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0;
                v___x_3916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1);
                v___x_3917_ = lean_nat_sub(v_endExclusive_3914_, v_startInclusive_3913_);
                v___x_3918_ = lean_nat_dec_le(v___x_3916_, v___x_3917_);
                if v___x_3918_ == 0 {
                    crate::leanh::lean_dec(v___x_3917_);
                    return v_s_3911_;
                } else {
                    v___x_3919_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3920_ = lean_nat_sub(v___x_3917_, v___x_3916_);
                    crate::leanh::lean_dec(v___x_3917_);
                    v___x_3921_ = lean_nat_add(v_startInclusive_3913_, v___x_3920_);
                    v___x_3922_ = lean_string_memcmp(
                        v_str_3912_,
                        v___x_3915_,
                        v___x_3921_,
                        v___x_3919_,
                        v___x_3916_,
                    );
                    crate::leanh::lean_dec(v___x_3921_);
                    if v___x_3922_ == 0 {
                        crate::leanh::lean_dec(v___x_3920_);
                        return v_s_3911_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_3913_);
                        crate::leanh::lean_inc_ref(v_str_3912_);
                        v___x_3923_ = l_String_Slice_pos_x21(v_s_3911_, v___x_3920_);
                        crate::leanh::lean_dec(v___x_3920_);
                        v_isSharedCheck_3931_ = (!crate::leanh::lean_is_exclusive(v_s_3911_)) as u8;
                        if v_isSharedCheck_3931_ == 0 {
                            v_unused_3932_ = crate::leanh::lean_ctor_get(v_s_3911_, 2);
                            crate::leanh::lean_dec(v_unused_3932_);
                            v_unused_3933_ = crate::leanh::lean_ctor_get(v_s_3911_, 1);
                            crate::leanh::lean_dec(v_unused_3933_);
                            v_unused_3934_ = crate::leanh::lean_ctor_get(v_s_3911_, 0);
                            crate::leanh::lean_dec(v_unused_3934_);
                            v___x_3925_ = v_s_3911_;
                            v_isShared_3926_ = v_isSharedCheck_3931_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_3911_);
                            v___x_3925_ = crate::leanh::lean_box(0);
                            v_isShared_3926_ = v_isSharedCheck_3931_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3927_ = lean_nat_add(v_startInclusive_3913_, v___x_3923_);
                crate::leanh::lean_dec(v___x_3923_);
                if v_isShared_3926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3925_, 2, v___x_3927_);
                    v___x_3929_ = v___x_3925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_str_3912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_startInclusive_3913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 2, v___x_3927_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0;
    v___x_3937_ = lean_string_utf8_byte_size(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(
    mut v_s_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_unused_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3939_ = crate::leanh::lean_ctor_get(v_s_3938_, 0);
                v_startInclusive_3940_ = crate::leanh::lean_ctor_get(v_s_3938_, 1);
                v_endExclusive_3941_ = crate::leanh::lean_ctor_get(v_s_3938_, 2);
                v___x_3942_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0;
                v___x_3943_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1);
                v___x_3944_ = lean_nat_sub(v_endExclusive_3941_, v_startInclusive_3940_);
                v___x_3945_ = lean_nat_dec_le(v___x_3943_, v___x_3944_);
                if v___x_3945_ == 0 {
                    crate::leanh::lean_dec(v___x_3944_);
                    return v_s_3938_;
                } else {
                    v___x_3946_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3947_ = lean_nat_sub(v___x_3944_, v___x_3943_);
                    crate::leanh::lean_dec(v___x_3944_);
                    v___x_3948_ = lean_nat_add(v_startInclusive_3940_, v___x_3947_);
                    v___x_3949_ = lean_string_memcmp(
                        v_str_3939_,
                        v___x_3942_,
                        v___x_3948_,
                        v___x_3946_,
                        v___x_3943_,
                    );
                    crate::leanh::lean_dec(v___x_3948_);
                    if v___x_3949_ == 0 {
                        crate::leanh::lean_dec(v___x_3947_);
                        return v_s_3938_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_3940_);
                        crate::leanh::lean_inc_ref(v_str_3939_);
                        v___x_3950_ = l_String_Slice_pos_x21(v_s_3938_, v___x_3947_);
                        crate::leanh::lean_dec(v___x_3947_);
                        v_isSharedCheck_3958_ = (!crate::leanh::lean_is_exclusive(v_s_3938_)) as u8;
                        if v_isSharedCheck_3958_ == 0 {
                            v_unused_3959_ = crate::leanh::lean_ctor_get(v_s_3938_, 2);
                            crate::leanh::lean_dec(v_unused_3959_);
                            v_unused_3960_ = crate::leanh::lean_ctor_get(v_s_3938_, 1);
                            crate::leanh::lean_dec(v_unused_3960_);
                            v_unused_3961_ = crate::leanh::lean_ctor_get(v_s_3938_, 0);
                            crate::leanh::lean_dec(v_unused_3961_);
                            v___x_3952_ = v_s_3938_;
                            v_isShared_3953_ = v_isSharedCheck_3958_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_3938_);
                            v___x_3952_ = crate::leanh::lean_box(0);
                            v_isShared_3953_ = v_isSharedCheck_3958_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3954_ = lean_nat_add(v_startInclusive_3940_, v___x_3950_);
                crate::leanh::lean_dec(v___x_3950_);
                if v_isShared_3953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3952_, 2, v___x_3954_);
                    v___x_3956_ = v___x_3952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_str_3939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_startInclusive_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 2, v___x_3954_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(
    mut v_s_3962_: *mut crate::leanh::LeanObject,
    mut v_pat_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3964_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3965_ = lean_string_utf8_byte_size(v_s_3962_);
    v___x_3966_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3966_, 0, v_s_3962_);
    crate::leanh::lean_ctor_set(v___x_3966_, 1, v___x_3964_);
    crate::leanh::lean_ctor_set(v___x_3966_, 2, v___x_3965_);
    v___x_3967_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(
    mut v_s_3968_: *mut crate::leanh::LeanObject,
    mut v_pat_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(
        v_s_3968_,
        v_pat_3969_,
    );
    crate::leanh::lean_dec_ref(v_pat_3969_);
    return v_res_3970_;
}
pub unsafe fn l_Lean_Linter_List_stripBinderName(
    mut v_s_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0;
    v___x_3973_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(
        v_s_3971_,
        v___x_3972_,
    );
    v___x_3974_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(v___x_3973_);
    v___x_3975_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(v___x_3974_);
    v___x_3976_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(v___x_3975_);
    v___x_3977_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(v___x_3976_);
    v_str_3978_ = crate::leanh::lean_ctor_get(v___x_3977_, 0);
    crate::leanh::lean_inc_ref(v_str_3978_);
    v_startInclusive_3979_ = crate::leanh::lean_ctor_get(v___x_3977_, 1);
    crate::leanh::lean_inc(v_startInclusive_3979_);
    v_endExclusive_3980_ = crate::leanh::lean_ctor_get(v___x_3977_, 2);
    crate::leanh::lean_inc(v_endExclusive_3980_);
    crate::leanh::lean_dec_ref(v___x_3977_);
    v___x_3981_ =
        lean_string_utf8_extract(v_str_3978_, v_startInclusive_3979_, v_endExclusive_3980_);
    crate::leanh::lean_dec(v_endExclusive_3980_);
    crate::leanh::lean_dec(v_startInclusive_3979_);
    crate::leanh::lean_dec_ref(v_str_3978_);
    return v___x_3981_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(
    mut v_pat_3982_: *mut crate::leanh::LeanObject,
    mut v_s_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3984_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v_s_3983_);
    return v___x_3984_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(
    mut v_pat_3985_: *mut crate::leanh::LeanObject,
    mut v_s_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(v_pat_3985_, v_s_3986_);
    crate::leanh::lean_dec_ref(v_pat_3985_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
    mut v___y_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = lean_st_ref_get(v___y_4038_);
    v_infoState_4041_ = crate::leanh::lean_ctor_get(v___x_4040_, 8);
    crate::leanh::lean_inc_ref(v_infoState_4041_);
    crate::leanh::lean_dec(v___x_4040_);
    v_trees_4042_ = crate::leanh::lean_ctor_get(v_infoState_4041_, 2);
    crate::leanh::lean_inc_ref(v_trees_4042_);
    crate::leanh::lean_dec_ref(v_infoState_4041_);
    v___x_4043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4043_, 0, v_trees_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
        v___y_4044_,
    );
    crate::leanh::lean_dec(v___y_4044_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
        v___y_4048_,
    );
    return v___x_4050_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4054_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(
        v___y_4051_,
        v___y_4052_,
    );
    crate::leanh::lean_dec(v___y_4052_);
    crate::leanh::lean_dec_ref(v___y_4051_);
    return v_res_4054_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(
    mut v_opts_4055_: *mut crate::leanh::LeanObject,
    mut v_opt_4056_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4057_ = crate::leanh::lean_ctor_get(v_opt_4056_, 0);
    v_defValue_4058_ = crate::leanh::lean_ctor_get(v_opt_4056_, 1);
    v_map_4059_ = crate::leanh::lean_ctor_get(v_opts_4055_, 0);
    v___x_4060_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4059_,
            v_name_4057_,
        );
    if crate::leanh::lean_obj_tag(v___x_4060_) == 0 {
        let mut v___x_4061_: u8 = 0;
        v___x_4061_ = (crate::leanh::lean_unbox(v_defValue_4058_) as u8);
        return v___x_4061_;
    } else {
        let mut v_val_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4062_ = crate::leanh::lean_ctor_get(v___x_4060_, 0);
        crate::leanh::lean_inc(v_val_4062_);
        crate::leanh::lean_dec_ref_known(v___x_4060_, 1);
        if crate::leanh::lean_obj_tag(v_val_4062_) == 1 {
            let mut v_v_4063_: u8 = 0;
            v_v_4063_ = crate::leanh::lean_ctor_get_uint8(v_val_4062_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4062_, 0);
            return v_v_4063_;
        } else {
            let mut v___x_4064_: u8 = 0;
            crate::leanh::lean_dec(v_val_4062_);
            v___x_4064_ = (crate::leanh::lean_unbox(v_defValue_4058_) as u8);
            return v___x_4064_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(
    mut v_opts_4065_: *mut crate::leanh::LeanObject,
    mut v_opt_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4067_: u8 = 0;
    let mut v_r_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4067_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_4065_, v_opt_4066_);
    crate::leanh::lean_dec_ref(v_opt_4066_);
    crate::leanh::lean_dec_ref(v_opts_4065_);
    v_r_4068_ = crate::leanh::lean_box((v_res_4067_) as usize);
    return v_r_4068_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(
    mut v___y_4070_: u8,
    mut v_suppressElabErrors_4071_: u8,
    mut v_x_4072_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4072_) == 1 {
        let mut v_pre_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4073_ = crate::leanh::lean_ctor_get(v_x_4072_, 0);
        if crate::leanh::lean_obj_tag(v_pre_4073_) == 0 {
            let mut v_str_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4076_: u8 = 0;
            v_str_4074_ = crate::leanh::lean_ctor_get(v_x_4072_, 1);
            v___x_4075_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0;
            v___x_4076_ = lean_string_dec_eq(v_str_4074_, v___x_4075_);
            if v___x_4076_ == 0 {
                return v___y_4070_;
            } else {
                return v_suppressElabErrors_4071_;
            }
        } else {
            return v___y_4070_;
        }
    } else {
        return v___y_4070_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed(
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4078_: *mut crate::leanh::LeanObject,
    mut v_x_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_12587__boxed_4080_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4081_: u8 = 0;
    let mut v_res_4082_: u8 = 0;
    let mut v_r_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_12587__boxed_4080_ = (crate::leanh::lean_unbox(v___y_4077_) as u8);
    v_suppressElabErrors_boxed_4081_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4078_) as u8);
    v_res_4082_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v___y_12587__boxed_4080_, v_suppressElabErrors_boxed_4081_, v_x_4079_);
    crate::leanh::lean_dec(v_x_4079_);
    v_r_4083_ = crate::leanh::lean_box((v_res_4082_) as usize);
    return v_r_4083_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4084_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0);
    v___x_4086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4085_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
    v___x_4088_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4089_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4089_, 0, v___x_4088_);
    crate::leanh::lean_ctor_set(v___x_4089_, 1, v___x_4088_);
    crate::leanh::lean_ctor_set(v___x_4089_, 2, v___x_4088_);
    crate::leanh::lean_ctor_set(v___x_4089_, 3, v___x_4088_);
    crate::leanh::lean_ctor_set(v___x_4089_, 4, v___x_4087_);
    crate::leanh::lean_ctor_set(v___x_4089_, 5, v___x_4087_);
    crate::leanh::lean_ctor_set(v___x_4089_, 6, v___x_4087_);
    crate::leanh::lean_ctor_set(v___x_4089_, 7, v___x_4087_);
    crate::leanh::lean_ctor_set(v___x_4089_, 8, v___x_4087_);
    crate::leanh::lean_ctor_set(v___x_4089_, 9, v___x_4087_);
    return v___x_4089_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4091_ = lean_mk_empty_array_with_capacity(v___x_4090_);
    v___x_4092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4092_, 0, v___x_4091_);
    return v___x_4092_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4093_: usize = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4093_ = 5usize;
    v___x_4094_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4095_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4096_ = lean_mk_empty_array_with_capacity(v___x_4095_);
    v___x_4097_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3);
    v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4098_, 0, v___x_4097_);
    crate::leanh::lean_ctor_set(v___x_4098_, 1, v___x_4096_);
    crate::leanh::lean_ctor_set(v___x_4098_, 2, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4098_, 3, v___x_4094_);
    crate::leanh::lean_ctor_set_usize(v___x_4098_, 4, v___x_4093_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4099_ = crate::leanh::lean_box(1);
    v___x_4100_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4);
    v___x_4101_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
    v___x_4102_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4102_, 0, v___x_4101_);
    crate::leanh::lean_ctor_set(v___x_4102_, 1, v___x_4100_);
    crate::leanh::lean_ctor_set(v___x_4102_, 2, v___x_4099_);
    return v___x_4102_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(
    mut v_msgData_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4106_ = lean_st_ref_get(v___y_4104_);
    v_env_4107_ = crate::leanh::lean_ctor_get(v___x_4106_, 0);
    crate::leanh::lean_inc_ref(v_env_4107_);
    crate::leanh::lean_dec(v___x_4106_);
    v___x_4108_ = lean_st_ref_get(v___y_4104_);
    v_scopes_4109_ = crate::leanh::lean_ctor_get(v___x_4108_, 2);
    crate::leanh::lean_inc(v_scopes_4109_);
    crate::leanh::lean_dec(v___x_4108_);
    v___x_4110_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_4111_ = l_List_head_x21___redArg(v___x_4110_, v_scopes_4109_);
    crate::leanh::lean_dec(v_scopes_4109_);
    v_opts_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 1);
    crate::leanh::lean_inc_ref(v_opts_4112_);
    crate::leanh::lean_dec(v___x_4111_);
    v___x_4113_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2);
    v___x_4114_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5);
    v___x_4115_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4115_, 0, v_env_4107_);
    crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4113_);
    crate::leanh::lean_ctor_set(v___x_4115_, 2, v___x_4114_);
    crate::leanh::lean_ctor_set(v___x_4115_, 3, v_opts_4112_);
    v___x_4116_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4116_, 0, v___x_4115_);
    crate::leanh::lean_ctor_set(v___x_4116_, 1, v_msgData_4103_);
    v___x_4117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(
    mut v_msgData_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_4118_, v___y_4119_);
    crate::leanh::lean_dec(v___y_4119_);
    return v_res_4121_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(
    mut v_ref_4123_: *mut crate::leanh::LeanObject,
    mut v_msgData_4124_: *mut crate::leanh::LeanObject,
    mut v_severity_4125_: u8,
    mut v_isSilent_4126_: u8,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: u8 = 0;
    let mut v___y_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4135_: u8 = 0;
    let mut v___y_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_a_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v___y_4194_: u8 = 0;
    let mut v___y_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: u8 = 0;
    let mut v___y_4197_: u8 = 0;
    let mut v___y_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4201_: u8 = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v___y_4222_: u8 = 0;
    let mut v___y_4223_: u8 = 0;
    let mut v___y_4224_: u8 = 0;
    let mut v___y_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4230_: u8 = 0;
    let mut v___y_4231_: u8 = 0;
    let mut v___y_4232_: u8 = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___x_4247_: u8 = 0;
    let mut v___y_4249_: u8 = 0;
    let mut v___y_4250_: u8 = 0;
    let mut v___y_4251_: u8 = 0;
    let mut v___y_4253_: u8 = 0;
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4247_ = 2;
                v___x_4265_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4125_, v___x_4247_);
                if v___x_4265_ == 0 {
                    v___y_4253_ = v___x_4265_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4124_);
                    v___x_4266_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4124_);
                    v___y_4253_ = v___x_4266_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_4139_ = l_Lean_Elab_Command_getScope___redArg(v___y_4138_);
                if crate::leanh::lean_obj_tag(v___x_4139_) == 0 {
                    v_a_4140_ = crate::leanh::lean_ctor_get(v___x_4139_, 0);
                    crate::leanh::lean_inc(v_a_4140_);
                    crate::leanh::lean_dec_ref_known(v___x_4139_, 1);
                    v___x_4141_ = l_Lean_Elab_Command_getScope___redArg(v___y_4138_);
                    if crate::leanh::lean_obj_tag(v___x_4141_) == 0 {
                        v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                        v_isSharedCheck_4176_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                        if v_isSharedCheck_4176_ == 0 {
                            v___x_4144_ = v___x_4141_;
                            v_isShared_4145_ = v_isSharedCheck_4176_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4142_);
                            crate::leanh::lean_dec(v___x_4141_);
                            v___x_4144_ = crate::leanh::lean_box(0);
                            v_isShared_4145_ = v_isSharedCheck_4176_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4140_);
                        crate::leanh::lean_dec(v___y_4137_);
                        crate::leanh::lean_dec_ref(v___y_4133_);
                        crate::leanh::lean_dec_ref(v___y_4131_);
                        v_a_4177_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                        v_isSharedCheck_4184_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                        if v_isSharedCheck_4184_ == 0 {
                            v___x_4179_ = v___x_4141_;
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4177_);
                            crate::leanh::lean_dec(v___x_4141_);
                            v___x_4179_ = crate::leanh::lean_box(0);
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4137_);
                    crate::leanh::lean_dec_ref(v___y_4133_);
                    crate::leanh::lean_dec_ref(v___y_4131_);
                    v_a_4185_ = crate::leanh::lean_ctor_get(v___x_4139_, 0);
                    v_isSharedCheck_4192_ = (!crate::leanh::lean_is_exclusive(v___x_4139_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v___x_4187_ = v___x_4139_;
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4185_);
                        crate::leanh::lean_dec(v___x_4139_);
                        v___x_4187_ = crate::leanh::lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4146_ = lean_st_ref_take(v___y_4138_);
                v_currNamespace_4147_ = crate::leanh::lean_ctor_get(v_a_4140_, 2);
                crate::leanh::lean_inc(v_currNamespace_4147_);
                crate::leanh::lean_dec(v_a_4140_);
                v_openDecls_4148_ = crate::leanh::lean_ctor_get(v_a_4142_, 3);
                crate::leanh::lean_inc(v_openDecls_4148_);
                crate::leanh::lean_dec(v_a_4142_);
                v_env_4149_ = crate::leanh::lean_ctor_get(v___x_4146_, 0);
                v_messages_4150_ = crate::leanh::lean_ctor_get(v___x_4146_, 1);
                v_scopes_4151_ = crate::leanh::lean_ctor_get(v___x_4146_, 2);
                v_usedQuotCtxts_4152_ = crate::leanh::lean_ctor_get(v___x_4146_, 3);
                v_nextMacroScope_4153_ = crate::leanh::lean_ctor_get(v___x_4146_, 4);
                v_maxRecDepth_4154_ = crate::leanh::lean_ctor_get(v___x_4146_, 5);
                v_ngen_4155_ = crate::leanh::lean_ctor_get(v___x_4146_, 6);
                v_auxDeclNGen_4156_ = crate::leanh::lean_ctor_get(v___x_4146_, 7);
                v_infoState_4157_ = crate::leanh::lean_ctor_get(v___x_4146_, 8);
                v_traceState_4158_ = crate::leanh::lean_ctor_get(v___x_4146_, 9);
                v_snapshotTasks_4159_ = crate::leanh::lean_ctor_get(v___x_4146_, 10);
                v_isSharedCheck_4175_ = (!crate::leanh::lean_is_exclusive(v___x_4146_)) as u8;
                if v_isSharedCheck_4175_ == 0 {
                    v___x_4161_ = v___x_4146_;
                    v_isShared_4162_ = v_isSharedCheck_4175_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4159_);
                    crate::leanh::lean_inc(v_traceState_4158_);
                    crate::leanh::lean_inc(v_infoState_4157_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4156_);
                    crate::leanh::lean_inc(v_ngen_4155_);
                    crate::leanh::lean_inc(v_maxRecDepth_4154_);
                    crate::leanh::lean_inc(v_nextMacroScope_4153_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_4152_);
                    crate::leanh::lean_inc(v_scopes_4151_);
                    crate::leanh::lean_inc(v_messages_4150_);
                    crate::leanh::lean_inc(v_env_4149_);
                    crate::leanh::lean_dec(v___x_4146_);
                    v___x_4161_ = crate::leanh::lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4163_, 0, v_currNamespace_4147_);
                crate::leanh::lean_ctor_set(v___x_4163_, 1, v_openDecls_4148_);
                v___x_4164_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                crate::leanh::lean_ctor_set(v___x_4164_, 1, v___y_4133_);
                crate::leanh::lean_inc_ref(v___y_4136_);
                crate::leanh::lean_inc_ref(v___y_4134_);
                v___x_4165_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4165_, 0, v___y_4134_);
                crate::leanh::lean_ctor_set(v___x_4165_, 1, v___y_4131_);
                crate::leanh::lean_ctor_set(v___x_4165_, 2, v___y_4137_);
                crate::leanh::lean_ctor_set(v___x_4165_, 3, v___y_4136_);
                crate::leanh::lean_ctor_set(v___x_4165_, 4, v___x_4164_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4135_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4132_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4126_,
                );
                v___x_4166_ = l_Lean_MessageLog_add(v___x_4165_, v_messages_4150_);
                if v_isShared_4162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4161_, 1, v___x_4166_);
                    v___x_4168_ = v___x_4161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_env_4149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_scopes_4151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 3, v_usedQuotCtxts_4152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 4, v_nextMacroScope_4153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 5, v_maxRecDepth_4154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 6, v_ngen_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 7, v_auxDeclNGen_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 8, v_infoState_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 9, v_traceState_4158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 10, v_snapshotTasks_4159_);
                    v___x_4168_ = v_reuseFailAlloc_4174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4169_ = lean_st_ref_set(v___y_4138_, v___x_4168_);
                v___x_4170_ = crate::leanh::lean_box(0);
                if v_isShared_4145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4144_, 0, v___x_4170_);
                    v___x_4172_ = v___x_4144_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
                    v___x_4172_ = v_reuseFailAlloc_4173_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4172_;
            }
            6 => {
                if v_isShared_4180_ == 0 {
                    v___x_4182_ = v___x_4179_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4182_;
            }
            8 => {
                if v_isShared_4188_ == 0 {
                    v___x_4190_ = v___x_4187_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4190_;
            }
            10 => {
                v_fileName_4199_ = crate::leanh::lean_ctor_get(v___y_4127_, 0);
                v_fileMap_4200_ = crate::leanh::lean_ctor_get(v___y_4127_, 1);
                v_suppressElabErrors_4201_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4127_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_4202_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4124_,
                    );
                v___x_4203_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_4202_, v___y_4128_);
                v_a_4204_ = crate::leanh::lean_ctor_get(v___x_4203_, 0);
                v_isSharedCheck_4220_ = (!crate::leanh::lean_is_exclusive(v___x_4203_)) as u8;
                if v_isSharedCheck_4220_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    v_isShared_4207_ = v_isSharedCheck_4220_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4204_);
                    crate::leanh::lean_dec(v___x_4203_);
                    v___x_4206_ = crate::leanh::lean_box(0);
                    v_isShared_4207_ = v_isSharedCheck_4220_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_4200_, 2);
                v___x_4208_ = l_Lean_FileMap_toPosition(v_fileMap_4200_, v___y_4195_);
                crate::leanh::lean_dec(v___y_4195_);
                v___x_4209_ = l_Lean_FileMap_toPosition(v_fileMap_4200_, v___y_4198_);
                crate::leanh::lean_dec(v___y_4198_);
                v___x_4210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                v___x_4211_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0;
                if v_suppressElabErrors_4201_ == 0 {
                    crate::leanh::lean_del_object(v___x_4206_);
                    v___y_4131_ = v___x_4208_;
                    v___y_4132_ = v___y_4196_;
                    v___y_4133_ = v_a_4204_;
                    v___y_4134_ = v_fileName_4199_;
                    v___y_4135_ = v___y_4197_;
                    v___y_4136_ = v___x_4211_;
                    v___y_4137_ = v___x_4210_;
                    v___y_4138_ = v___y_4128_;
                    state = 1;
                    continue;
                } else {
                    v___x_4212_ = crate::leanh::lean_box((v___y_4194_) as usize);
                    v___x_4213_ = crate::leanh::lean_box((v_suppressElabErrors_4201_) as usize);
                    v___f_4214_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4214_, 0, v___x_4212_);
                    crate::leanh::lean_closure_set(v___f_4214_, 1, v___x_4213_);
                    crate::leanh::lean_inc(v_a_4204_);
                    v___x_4215_ = l_Lean_MessageData_hasTag(v___f_4214_, v_a_4204_);
                    if v___x_4215_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4210_, 1);
                        crate::leanh::lean_dec_ref(v___x_4208_);
                        crate::leanh::lean_dec(v_a_4204_);
                        v___x_4216_ = crate::leanh::lean_box(0);
                        if v_isShared_4207_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4206_, 0, v___x_4216_);
                            v___x_4218_ = v___x_4206_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4219_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
                            v___x_4218_ = v_reuseFailAlloc_4219_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4206_);
                        v___y_4131_ = v___x_4208_;
                        v___y_4132_ = v___y_4196_;
                        v___y_4133_ = v_a_4204_;
                        v___y_4134_ = v_fileName_4199_;
                        v___y_4135_ = v___y_4197_;
                        v___y_4136_ = v___x_4211_;
                        v___y_4137_ = v___x_4210_;
                        v___y_4138_ = v___y_4128_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_4218_;
            }
            13 => {
                v___x_4227_ = l_Lean_Syntax_getTailPos_x3f(v___y_4225_, v___y_4224_);
                crate::leanh::lean_dec(v___y_4225_);
                if crate::leanh::lean_obj_tag(v___x_4227_) == 0 {
                    crate::leanh::lean_inc(v___y_4226_);
                    v___y_4194_ = v___y_4222_;
                    v___y_4195_ = v___y_4226_;
                    v___y_4196_ = v___y_4223_;
                    v___y_4197_ = v___y_4224_;
                    v___y_4198_ = v___y_4226_;
                    state = 10;
                    continue;
                } else {
                    v_val_4228_ = crate::leanh::lean_ctor_get(v___x_4227_, 0);
                    crate::leanh::lean_inc(v_val_4228_);
                    crate::leanh::lean_dec_ref_known(v___x_4227_, 1);
                    v___y_4194_ = v___y_4222_;
                    v___y_4195_ = v___y_4226_;
                    v___y_4196_ = v___y_4223_;
                    v___y_4197_ = v___y_4224_;
                    v___y_4198_ = v_val_4228_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_4233_ = l_Lean_Elab_Command_getRef___redArg(v___y_4127_);
                if crate::leanh::lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
                    crate::leanh::lean_inc(v_a_4234_);
                    crate::leanh::lean_dec_ref_known(v___x_4233_, 1);
                    v_ref_4235_ = l_Lean_replaceRef(v_ref_4123_, v_a_4234_);
                    crate::leanh::lean_dec(v_a_4234_);
                    v___x_4236_ = l_Lean_Syntax_getPos_x3f(v_ref_4235_, v___y_4231_);
                    if crate::leanh::lean_obj_tag(v___x_4236_) == 0 {
                        v___x_4237_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_4222_ = v___y_4230_;
                        v___y_4223_ = v___y_4232_;
                        v___y_4224_ = v___y_4231_;
                        v___y_4225_ = v_ref_4235_;
                        v___y_4226_ = v___x_4237_;
                        state = 13;
                        continue;
                    } else {
                        v_val_4238_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                        crate::leanh::lean_inc(v_val_4238_);
                        crate::leanh::lean_dec_ref_known(v___x_4236_, 1);
                        v___y_4222_ = v___y_4230_;
                        v___y_4223_ = v___y_4232_;
                        v___y_4224_ = v___y_4231_;
                        v___y_4225_ = v_ref_4235_;
                        v___y_4226_ = v_val_4238_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4124_);
                    v_a_4239_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
                    v_isSharedCheck_4246_ = (!crate::leanh::lean_is_exclusive(v___x_4233_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___x_4233_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4239_);
                        crate::leanh::lean_dec(v___x_4233_);
                        v___x_4241_ = crate::leanh::lean_box(0);
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_4242_ == 0 {
                    v___x_4244_ = v___x_4241_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
                    v___x_4244_ = v_reuseFailAlloc_4245_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4244_;
            }
            17 => {
                if v___y_4251_ == 0 {
                    v___y_4230_ = v___y_4249_;
                    v___y_4231_ = v___y_4250_;
                    v___y_4232_ = v_severity_4125_;
                    state = 14;
                    continue;
                } else {
                    v___y_4230_ = v___y_4249_;
                    v___y_4231_ = v___y_4250_;
                    v___y_4232_ = v___x_4247_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_4253_ == 0 {
                    v___x_4254_ = lean_st_ref_get(v___y_4128_);
                    v_scopes_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 2);
                    crate::leanh::lean_inc(v_scopes_4255_);
                    crate::leanh::lean_dec(v___x_4254_);
                    v___x_4256_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_4257_ = l_List_head_x21___redArg(v___x_4256_, v_scopes_4255_);
                    crate::leanh::lean_dec(v_scopes_4255_);
                    v_opts_4258_ = crate::leanh::lean_ctor_get(v___x_4257_, 1);
                    crate::leanh::lean_inc_ref(v_opts_4258_);
                    crate::leanh::lean_dec(v___x_4257_);
                    v___x_4259_ = 1;
                    v___x_4260_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4125_, v___x_4259_);
                    if v___x_4260_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_4258_);
                        v___y_4249_ = v___y_4253_;
                        v___y_4250_ = v___y_4253_;
                        v___y_4251_ = v___x_4260_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4261_ = l_Lean_warningAsError;
                        v___x_4262_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_4258_, v___x_4261_);
                        crate::leanh::lean_dec_ref(v_opts_4258_);
                        v___y_4249_ = v___y_4253_;
                        v___y_4250_ = v___y_4253_;
                        v___y_4251_ = v___x_4262_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4124_);
                    v___x_4263_ = crate::leanh::lean_box(0);
                    v___x_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                    return v___x_4264_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(
    mut v_ref_4267_: *mut crate::leanh::LeanObject,
    mut v_msgData_4268_: *mut crate::leanh::LeanObject,
    mut v_severity_4269_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4274_: u8 = 0;
    let mut v_isSilent_boxed_4275_: u8 = 0;
    let mut v_res_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4274_ = (crate::leanh::lean_unbox(v_severity_4269_) as u8);
    v_isSilent_boxed_4275_ = (crate::leanh::lean_unbox(v_isSilent_4270_) as u8);
    v_res_4276_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_4267_, v_msgData_4268_, v_severity_boxed_4274_, v_isSilent_boxed_4275_, v___y_4271_, v___y_4272_);
    crate::leanh::lean_dec(v___y_4272_);
    crate::leanh::lean_dec_ref(v___y_4271_);
    crate::leanh::lean_dec(v_ref_4267_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(
    mut v_ref_4277_: *mut crate::leanh::LeanObject,
    mut v_msgData_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = 1;
    v___x_4283_ = 0;
    v___x_4284_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_4277_, v_msgData_4278_, v___x_4282_, v___x_4283_, v___y_4279_, v___y_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(
    mut v_ref_4285_: *mut crate::leanh::LeanObject,
    mut v_msgData_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4290_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_4285_, v_msgData_4286_, v___y_4287_, v___y_4288_);
    crate::leanh::lean_dec(v___y_4288_);
    crate::leanh::lean_dec_ref(v___y_4287_);
    crate::leanh::lean_dec(v_ref_4285_);
    return v_res_4290_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0;
    v___x_4293_ = l_Lean_stringToMessageData(v___x_4292_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2;
    v___x_4296_ = l_Lean_stringToMessageData(v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
    mut v_linterOption_4297_: *mut crate::leanh::LeanObject,
    mut v_stx_4298_: *mut crate::leanh::LeanObject,
    mut v_msg_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_unused_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4303_ = crate::leanh::lean_ctor_get(v_linterOption_4297_, 0);
                v_isSharedCheck_4320_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_4297_)) as u8;
                if v_isSharedCheck_4320_ == 0 {
                    v_unused_4321_ = crate::leanh::lean_ctor_get(v_linterOption_4297_, 1);
                    crate::leanh::lean_dec(v_unused_4321_);
                    v___x_4305_ = v_linterOption_4297_;
                    v_isShared_4306_ = v_isSharedCheck_4320_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_4303_);
                    crate::leanh::lean_dec(v_linterOption_4297_);
                    v___x_4305_ = crate::leanh::lean_box(0);
                    v_isShared_4306_ = v_isSharedCheck_4320_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4307_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
                crate::leanh::lean_inc(v_name_4303_);
                v___x_4308_ = l_Lean_MessageData_ofName(v_name_4303_);
                if v_isShared_4306_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4305_, 7);
                    crate::leanh::lean_ctor_set(v___x_4305_, 1, v___x_4308_);
                    crate::leanh::lean_ctor_set(v___x_4305_, 0, v___x_4307_);
                    v___x_4310_ = v___x_4305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 1, v___x_4308_);
                    v___x_4310_ = v_reuseFailAlloc_4319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
                v___x_4312_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4312_, 0, v___x_4310_);
                crate::leanh::lean_ctor_set(v___x_4312_, 1, v___x_4311_);
                v_disable_4313_ = l_Lean_MessageData_note(v___x_4312_);
                v___x_4314_ = l_Lean_Linter_linterMessageTag;
                v___x_4315_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4315_, 0, v_msg_4299_);
                crate::leanh::lean_ctor_set(v___x_4315_, 1, v_disable_4313_);
                v___x_4316_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4316_, 0, v___x_4314_);
                crate::leanh::lean_ctor_set(v___x_4316_, 1, v___x_4315_);
                v___x_4317_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4317_, 0, v_name_4303_);
                crate::leanh::lean_ctor_set(v___x_4317_, 1, v___x_4316_);
                v___x_4318_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_4298_, v___x_4317_, v___y_4300_, v___y_4301_);
                return v___x_4318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(
    mut v_linterOption_4322_: *mut crate::leanh::LeanObject,
    mut v_stx_4323_: *mut crate::leanh::LeanObject,
    mut v_msg_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4328_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
        v_linterOption_4322_,
        v_stx_4323_,
        v_msg_4324_,
        v___y_4325_,
        v___y_4326_,
    );
    crate::leanh::lean_dec(v___y_4326_);
    crate::leanh::lean_dec_ref(v___y_4325_);
    crate::leanh::lean_dec(v_stx_4323_);
    return v_res_4328_;
}
pub unsafe fn l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_x_4330_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4331_: u8 = 0;
    let mut v_head_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4330_) == 0 {
                    v___x_4331_ = 0;
                    return v___x_4331_;
                } else {
                    v_head_4332_ = crate::leanh::lean_ctor_get(v_x_4330_, 0);
                    v_tail_4333_ = crate::leanh::lean_ctor_get(v_x_4330_, 1);
                    v___x_4334_ = lean_string_dec_eq(v_a_4329_, v_head_4332_);
                    if v___x_4334_ == 0 {
                        v_x_4330_ = v_tail_4333_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4334_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1___boxed(
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_x_4337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4338_: u8 = 0;
    let mut v_r_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_4336_, v_x_4337_);
    crate::leanh::lean_dec(v_x_4337_);
    crate::leanh::lean_dec_ref(v_a_4336_);
    v_r_4339_ = crate::leanh::lean_box((v_res_4338_) as usize);
    return v_r_4339_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4341_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0;
    v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
    return v___x_4342_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
    mut v_as_x27_4343_: *mut crate::leanh::LeanObject,
    mut v_b_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4343_) == 0 {
                    v___x_4348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4348_, 0, v_b_4344_);
                    return v___x_4348_;
                } else {
                    v_head_4349_ = crate::leanh::lean_ctor_get(v_as_x27_4343_, 0);
                    v_tail_4350_ = crate::leanh::lean_ctor_get(v_as_x27_4343_, 1);
                    v_fst_4351_ = crate::leanh::lean_ctor_get(v_head_4349_, 0);
                    v_snd_4352_ = crate::leanh::lean_ctor_get(v_head_4349_, 1);
                    v___x_4353_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_snd_4352_) == 1 {
                        v_str_4354_ = crate::leanh::lean_ctor_get(v_snd_4352_, 1);
                        v___x_4355_ = l_Lean_Linter_List_allowedWidths;
                        crate::leanh::lean_inc_ref(v_str_4354_);
                        v___x_4356_ = l_Lean_Linter_List_stripBinderName(v_str_4354_);
                        v___x_4357_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4356_,
                            v___x_4355_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4356_);
                        if v___x_4357_ == 0 {
                            v___x_4358_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
                            crate::leanh::lean_inc_ref(v_str_4354_);
                            v___x_4360_ = l_Lean_stringToMessageData(v_str_4354_);
                            v___x_4361_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4359_);
                            crate::leanh::lean_ctor_set(v___x_4361_, 1, v___x_4360_);
                            v___x_4362_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4358_,
                                    v_fst_4351_,
                                    v___x_4361_,
                                    v___y_4345_,
                                    v___y_4346_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_4362_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4362_, 1);
                                v_as_x27_4343_ = v_tail_4350_;
                                v_b_4344_ = v___x_4353_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_4362_;
                            }
                        } else {
                            v_as_x27_4343_ = v_tail_4350_;
                            v_b_4344_ = v___x_4353_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_4343_ = v_tail_4350_;
                        v_b_4344_ = v___x_4353_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___boxed(
    mut v_as_x27_4366_: *mut crate::leanh::LeanObject,
    mut v_b_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4371_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
        v_as_x27_4366_,
        v_b_4367_,
        v___y_4368_,
        v___y_4369_,
    );
    crate::leanh::lean_dec(v___y_4369_);
    crate::leanh::lean_dec_ref(v___y_4368_);
    crate::leanh::lean_dec(v_as_x27_4366_);
    return v_res_4371_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4373_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0;
    v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
    return v___x_4374_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
    mut v_as_x27_4375_: *mut crate::leanh::LeanObject,
    mut v_b_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4375_) == 0 {
                    v___x_4380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4380_, 0, v_b_4376_);
                    return v___x_4380_;
                } else {
                    v_head_4381_ = crate::leanh::lean_ctor_get(v_as_x27_4375_, 0);
                    v_tail_4382_ = crate::leanh::lean_ctor_get(v_as_x27_4375_, 1);
                    v_fst_4383_ = crate::leanh::lean_ctor_get(v_head_4381_, 0);
                    v_snd_4384_ = crate::leanh::lean_ctor_get(v_head_4381_, 1);
                    v___x_4385_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_snd_4384_) == 1 {
                        v_str_4386_ = crate::leanh::lean_ctor_get(v_snd_4384_, 1);
                        v___x_4387_ = l_Lean_Linter_List_allowedBitVecWidths;
                        crate::leanh::lean_inc_ref(v_str_4386_);
                        v___x_4388_ = l_Lean_Linter_List_stripBinderName(v_str_4386_);
                        v___x_4389_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4388_,
                            v___x_4387_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4388_);
                        if v___x_4389_ == 0 {
                            v___x_4390_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4391_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
                            crate::leanh::lean_inc_ref(v_str_4386_);
                            v___x_4392_ = l_Lean_stringToMessageData(v_str_4386_);
                            v___x_4393_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4393_, 0, v___x_4391_);
                            crate::leanh::lean_ctor_set(v___x_4393_, 1, v___x_4392_);
                            v___x_4394_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4390_,
                                    v_fst_4383_,
                                    v___x_4393_,
                                    v___y_4377_,
                                    v___y_4378_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_4394_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4394_, 1);
                                v_as_x27_4375_ = v_tail_4382_;
                                v_b_4376_ = v___x_4385_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_4394_;
                            }
                        } else {
                            v_as_x27_4375_ = v_tail_4382_;
                            v_b_4376_ = v___x_4385_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_4375_ = v_tail_4382_;
                        v_b_4376_ = v___x_4385_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___boxed(
    mut v_as_x27_4398_: *mut crate::leanh::LeanObject,
    mut v_b_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4403_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
        v_as_x27_4398_,
        v_b_4399_,
        v___y_4400_,
        v___y_4401_,
    );
    crate::leanh::lean_dec(v___y_4401_);
    crate::leanh::lean_dec_ref(v___y_4400_);
    crate::leanh::lean_dec(v_as_x27_4398_);
    return v_res_4403_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4405_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0;
    v___x_4406_ = l_Lean_stringToMessageData(v___x_4405_);
    return v___x_4406_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
    mut v_as_x27_4407_: *mut crate::leanh::LeanObject,
    mut v_b_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4407_) == 0 {
                    v___x_4412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4412_, 0, v_b_4408_);
                    return v___x_4412_;
                } else {
                    v_head_4413_ = crate::leanh::lean_ctor_get(v_as_x27_4407_, 0);
                    v_tail_4414_ = crate::leanh::lean_ctor_get(v_as_x27_4407_, 1);
                    v_fst_4415_ = crate::leanh::lean_ctor_get(v_head_4413_, 0);
                    v_snd_4416_ = crate::leanh::lean_ctor_get(v_head_4413_, 1);
                    v___x_4417_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_snd_4416_) == 1 {
                        v_str_4418_ = crate::leanh::lean_ctor_get(v_snd_4416_, 1);
                        v___x_4419_ = l_Lean_Linter_List_allowedIndices;
                        crate::leanh::lean_inc_ref(v_str_4418_);
                        v___x_4420_ = l_Lean_Linter_List_stripBinderName(v_str_4418_);
                        v___x_4421_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4420_,
                            v___x_4419_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4420_);
                        if v___x_4421_ == 0 {
                            v___x_4422_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4423_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
                            crate::leanh::lean_inc_ref(v_str_4418_);
                            v___x_4424_ = l_Lean_stringToMessageData(v_str_4418_);
                            v___x_4425_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4423_);
                            crate::leanh::lean_ctor_set(v___x_4425_, 1, v___x_4424_);
                            v___x_4426_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4422_,
                                    v_fst_4415_,
                                    v___x_4425_,
                                    v___y_4409_,
                                    v___y_4410_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_4426_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4426_, 1);
                                v_as_x27_4407_ = v_tail_4414_;
                                v_b_4408_ = v___x_4417_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_4426_;
                            }
                        } else {
                            v_as_x27_4407_ = v_tail_4414_;
                            v_b_4408_ = v___x_4417_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_4407_ = v_tail_4414_;
                        v_b_4408_ = v___x_4417_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___boxed(
    mut v_as_x27_4430_: *mut crate::leanh::LeanObject,
    mut v_b_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
        v_as_x27_4430_,
        v_b_4431_,
        v___y_4432_,
        v___y_4433_,
    );
    crate::leanh::lean_dec(v___y_4433_);
    crate::leanh::lean_dec_ref(v___y_4432_);
    crate::leanh::lean_dec(v_as_x27_4430_);
    return v_res_4435_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(
    mut v_as_4439_: *mut crate::leanh::LeanObject,
    mut v_sz_4440_: usize,
    mut v_i_4441_: usize,
    mut v_b_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: usize = 0;
    let mut v___x_4458_: usize = 0;
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4446_ = lean_usize_dec_lt(v_i_4441_, v_sz_4440_);
                if v___x_4446_ == 0 {
                    v___x_4447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4447_, 0, v_b_4442_);
                    return v___x_4447_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4442_);
                    v___x_4448_ = crate::leanh::lean_box(0);
                    v_a_4449_ = lean_array_uget_borrowed(v_as_4439_, v_i_4441_);
                    crate::leanh::lean_inc(v_a_4449_);
                    v___x_4450_ = l_Lean_Linter_List_numericalIndices(v_a_4449_);
                    v___x_4451_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4450_, v___x_4448_, v___y_4443_, v___y_4444_);
                    crate::leanh::lean_dec(v___x_4450_);
                    if crate::leanh::lean_obj_tag(v___x_4451_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4451_, 1);
                        crate::leanh::lean_inc(v_a_4449_);
                        v___x_4452_ = l_Lean_Linter_List_numericalWidths(v_a_4449_);
                        v___x_4453_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4452_, v___x_4448_, v___y_4443_, v___y_4444_);
                        crate::leanh::lean_dec(v___x_4452_);
                        if crate::leanh::lean_obj_tag(v___x_4453_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4453_, 1);
                            crate::leanh::lean_inc(v_a_4449_);
                            v___x_4454_ = l_Lean_Linter_List_bitVecWidths(v_a_4449_);
                            v___x_4455_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4454_, v___x_4448_, v___y_4443_, v___y_4444_);
                            crate::leanh::lean_dec(v___x_4454_);
                            if crate::leanh::lean_obj_tag(v___x_4455_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4455_, 1);
                                v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                v___x_4457_ = 1usize;
                                v___x_4458_ = lean_usize_add(v_i_4441_, v___x_4457_);
                                v_i_4441_ = v___x_4458_;
                                v_b_4442_ = v___x_4456_;
                                state = 0;
                                continue;
                            } else {
                                v_a_4460_ = crate::leanh::lean_ctor_get(v___x_4455_, 0);
                                v_isSharedCheck_4467_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4455_)) as u8;
                                if v_isSharedCheck_4467_ == 0 {
                                    v___x_4462_ = v___x_4455_;
                                    v_isShared_4463_ = v_isSharedCheck_4467_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4460_);
                                    crate::leanh::lean_dec(v___x_4455_);
                                    v___x_4462_ = crate::leanh::lean_box(0);
                                    v_isShared_4463_ = v_isSharedCheck_4467_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4468_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                            v_isSharedCheck_4475_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4453_)) as u8;
                            if v_isSharedCheck_4475_ == 0 {
                                v___x_4470_ = v___x_4453_;
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4468_);
                                crate::leanh::lean_dec(v___x_4453_);
                                v___x_4470_ = crate::leanh::lean_box(0);
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4476_ = crate::leanh::lean_ctor_get(v___x_4451_, 0);
                        v_isSharedCheck_4483_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4478_ = v___x_4451_;
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4476_);
                            crate::leanh::lean_dec(v___x_4451_);
                            v___x_4478_ = crate::leanh::lean_box(0);
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4463_ == 0 {
                    v___x_4465_ = v___x_4462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
                    v___x_4465_ = v_reuseFailAlloc_4466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4465_;
            }
            3 => {
                if v_isShared_4471_ == 0 {
                    v___x_4473_ = v___x_4470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4473_;
            }
            5 => {
                if v_isShared_4479_ == 0 {
                    v___x_4481_ = v___x_4478_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___boxed(
    mut v_as_4484_: *mut crate::leanh::LeanObject,
    mut v_sz_4485_: *mut crate::leanh::LeanObject,
    mut v_i_4486_: *mut crate::leanh::LeanObject,
    mut v_b_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4491_: usize = 0;
    let mut v_i_boxed_4492_: usize = 0;
    let mut v_res_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4491_ = crate::leanh::lean_unbox_usize(v_sz_4485_);
    crate::leanh::lean_dec(v_sz_4485_);
    v_i_boxed_4492_ = crate::leanh::lean_unbox_usize(v_i_4486_);
    crate::leanh::lean_dec(v_i_4486_);
    v_res_4493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_4484_, v_sz_boxed_4491_, v_i_boxed_4492_, v_b_4487_, v___y_4488_, v___y_4489_);
    crate::leanh::lean_dec(v___y_4489_);
    crate::leanh::lean_dec_ref(v___y_4488_);
    crate::leanh::lean_dec_ref(v_as_4484_);
    return v_res_4493_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(
    mut v_as_4494_: *mut crate::leanh::LeanObject,
    mut v_sz_4495_: usize,
    mut v_i_4496_: usize,
    mut v_b_4497_: *mut crate::leanh::LeanObject,
    mut v___y_4498_: *mut crate::leanh::LeanObject,
    mut v___y_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: usize = 0;
    let mut v___x_4513_: usize = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_a_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = lean_usize_dec_lt(v_i_4496_, v_sz_4495_);
                if v___x_4501_ == 0 {
                    v___x_4502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4502_, 0, v_b_4497_);
                    return v___x_4502_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4497_);
                    v___x_4503_ = crate::leanh::lean_box(0);
                    v_a_4504_ = lean_array_uget_borrowed(v_as_4494_, v_i_4496_);
                    crate::leanh::lean_inc(v_a_4504_);
                    v___x_4505_ = l_Lean_Linter_List_numericalIndices(v_a_4504_);
                    v___x_4506_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4505_, v___x_4503_, v___y_4498_, v___y_4499_);
                    crate::leanh::lean_dec(v___x_4505_);
                    if crate::leanh::lean_obj_tag(v___x_4506_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4506_, 1);
                        crate::leanh::lean_inc(v_a_4504_);
                        v___x_4507_ = l_Lean_Linter_List_numericalWidths(v_a_4504_);
                        v___x_4508_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4507_, v___x_4503_, v___y_4498_, v___y_4499_);
                        crate::leanh::lean_dec(v___x_4507_);
                        if crate::leanh::lean_obj_tag(v___x_4508_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4508_, 1);
                            crate::leanh::lean_inc(v_a_4504_);
                            v___x_4509_ = l_Lean_Linter_List_bitVecWidths(v_a_4504_);
                            v___x_4510_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4509_, v___x_4503_, v___y_4498_, v___y_4499_);
                            crate::leanh::lean_dec(v___x_4509_);
                            if crate::leanh::lean_obj_tag(v___x_4510_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4510_, 1);
                                v___x_4511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                v___x_4512_ = 1usize;
                                v___x_4513_ = lean_usize_add(v_i_4496_, v___x_4512_);
                                v___x_4514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_4494_, v_sz_4495_, v___x_4513_, v___x_4511_, v___y_4498_, v___y_4499_);
                                return v___x_4514_;
                            } else {
                                v_a_4515_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                                v_isSharedCheck_4522_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4510_)) as u8;
                                if v_isSharedCheck_4522_ == 0 {
                                    v___x_4517_ = v___x_4510_;
                                    v_isShared_4518_ = v_isSharedCheck_4522_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4515_);
                                    crate::leanh::lean_dec(v___x_4510_);
                                    v___x_4517_ = crate::leanh::lean_box(0);
                                    v_isShared_4518_ = v_isSharedCheck_4522_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4523_ = crate::leanh::lean_ctor_get(v___x_4508_, 0);
                            v_isSharedCheck_4530_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4508_)) as u8;
                            if v_isSharedCheck_4530_ == 0 {
                                v___x_4525_ = v___x_4508_;
                                v_isShared_4526_ = v_isSharedCheck_4530_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4523_);
                                crate::leanh::lean_dec(v___x_4508_);
                                v___x_4525_ = crate::leanh::lean_box(0);
                                v_isShared_4526_ = v_isSharedCheck_4530_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4506_, 0);
                        v_isSharedCheck_4538_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4538_ == 0 {
                            v___x_4533_ = v___x_4506_;
                            v_isShared_4534_ = v_isSharedCheck_4538_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4531_);
                            crate::leanh::lean_dec(v___x_4506_);
                            v___x_4533_ = crate::leanh::lean_box(0);
                            v_isShared_4534_ = v_isSharedCheck_4538_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4518_ == 0 {
                    v___x_4520_ = v___x_4517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4520_;
            }
            3 => {
                if v_isShared_4526_ == 0 {
                    v___x_4528_ = v___x_4525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
                    v___x_4528_ = v_reuseFailAlloc_4529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4528_;
            }
            5 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10___boxed(
    mut v_as_4539_: *mut crate::leanh::LeanObject,
    mut v_sz_4540_: *mut crate::leanh::LeanObject,
    mut v_i_4541_: *mut crate::leanh::LeanObject,
    mut v_b_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4546_: usize = 0;
    let mut v_i_boxed_4547_: usize = 0;
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4546_ = crate::leanh::lean_unbox_usize(v_sz_4540_);
    crate::leanh::lean_dec(v_sz_4540_);
    v_i_boxed_4547_ = crate::leanh::lean_unbox_usize(v_i_4541_);
    crate::leanh::lean_dec(v_i_4541_);
    v_res_4548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_4539_, v_sz_boxed_4546_, v_i_boxed_4547_, v_b_4542_, v___y_4543_, v___y_4544_);
    crate::leanh::lean_dec(v___y_4544_);
    crate::leanh::lean_dec_ref(v___y_4543_);
    crate::leanh::lean_dec_ref(v_as_4539_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(
    mut v_init_4549_: *mut crate::leanh::LeanObject,
    mut v_n_4550_: *mut crate::leanh::LeanObject,
    mut v_b_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v_fst_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4583_: u8 = 0;
    let mut v_vs_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4587_: usize = 0;
    let mut v___x_4588_: usize = 0;
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_fst_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_a_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_4550_) == 0 {
                    v_cs_4555_ = crate::leanh::lean_ctor_get(v_n_4550_, 0);
                    v___x_4556_ = crate::leanh::lean_box(0);
                    v___x_4557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4557_, 0, v___x_4556_);
                    crate::leanh::lean_ctor_set(v___x_4557_, 1, v_b_4551_);
                    v_sz_4558_ = lean_array_size(v_cs_4555_);
                    v___x_4559_ = 0usize;
                    v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_4549_, v_cs_4555_, v_sz_4558_, v___x_4559_, v___x_4557_, v___y_4552_, v___y_4553_);
                    if crate::leanh::lean_obj_tag(v___x_4560_) == 0 {
                        v_a_4561_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                        v_isSharedCheck_4575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                        if v_isSharedCheck_4575_ == 0 {
                            v___x_4563_ = v___x_4560_;
                            v_isShared_4564_ = v_isSharedCheck_4575_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4561_);
                            crate::leanh::lean_dec(v___x_4560_);
                            v___x_4563_ = crate::leanh::lean_box(0);
                            v_isShared_4564_ = v_isSharedCheck_4575_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4576_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                        v_isSharedCheck_4583_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                        if v_isSharedCheck_4583_ == 0 {
                            v___x_4578_ = v___x_4560_;
                            v_isShared_4579_ = v_isSharedCheck_4583_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4576_);
                            crate::leanh::lean_dec(v___x_4560_);
                            v___x_4578_ = crate::leanh::lean_box(0);
                            v_isShared_4579_ = v_isSharedCheck_4583_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4584_ = crate::leanh::lean_ctor_get(v_n_4550_, 0);
                    v___x_4585_ = crate::leanh::lean_box(0);
                    v___x_4586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4585_);
                    crate::leanh::lean_ctor_set(v___x_4586_, 1, v_b_4551_);
                    v_sz_4587_ = lean_array_size(v_vs_4584_);
                    v___x_4588_ = 0usize;
                    v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_4584_, v_sz_4587_, v___x_4588_, v___x_4586_, v___y_4552_, v___y_4553_);
                    if crate::leanh::lean_obj_tag(v___x_4589_) == 0 {
                        v_a_4590_ = crate::leanh::lean_ctor_get(v___x_4589_, 0);
                        v_isSharedCheck_4604_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4589_)) as u8;
                        if v_isSharedCheck_4604_ == 0 {
                            v___x_4592_ = v___x_4589_;
                            v_isShared_4593_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4590_);
                            crate::leanh::lean_dec(v___x_4589_);
                            v___x_4592_ = crate::leanh::lean_box(0);
                            v_isShared_4593_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4605_ = crate::leanh::lean_ctor_get(v___x_4589_, 0);
                        v_isSharedCheck_4612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4589_)) as u8;
                        if v_isSharedCheck_4612_ == 0 {
                            v___x_4607_ = v___x_4589_;
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4605_);
                            crate::leanh::lean_dec(v___x_4589_);
                            v___x_4607_ = crate::leanh::lean_box(0);
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4565_ = crate::leanh::lean_ctor_get(v_a_4561_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4565_) == 0 {
                    v_snd_4566_ = crate::leanh::lean_ctor_get(v_a_4561_, 1);
                    crate::leanh::lean_inc(v_snd_4566_);
                    crate::leanh::lean_dec(v_a_4561_);
                    v___x_4567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4567_, 0, v_snd_4566_);
                    if v_isShared_4564_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4563_, 0, v___x_4567_);
                        v___x_4569_ = v___x_4563_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                        v___x_4569_ = v_reuseFailAlloc_4570_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4565_);
                    crate::leanh::lean_dec(v_a_4561_);
                    v_val_4571_ = crate::leanh::lean_ctor_get(v_fst_4565_, 0);
                    crate::leanh::lean_inc(v_val_4571_);
                    crate::leanh::lean_dec_ref_known(v_fst_4565_, 1);
                    if v_isShared_4564_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4563_, 0, v_val_4571_);
                        v___x_4573_ = v___x_4563_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_val_4571_);
                        v___x_4573_ = v_reuseFailAlloc_4574_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4569_;
            }
            3 => {
                return v___x_4573_;
            }
            4 => {
                if v_isShared_4579_ == 0 {
                    v___x_4581_ = v___x_4578_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
                    v___x_4581_ = v_reuseFailAlloc_4582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4581_;
            }
            6 => {
                v_fst_4594_ = crate::leanh::lean_ctor_get(v_a_4590_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4594_) == 0 {
                    v_snd_4595_ = crate::leanh::lean_ctor_get(v_a_4590_, 1);
                    crate::leanh::lean_inc(v_snd_4595_);
                    crate::leanh::lean_dec(v_a_4590_);
                    v___x_4596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4596_, 0, v_snd_4595_);
                    if v_isShared_4593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4592_, 0, v___x_4596_);
                        v___x_4598_ = v___x_4592_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
                        v___x_4598_ = v_reuseFailAlloc_4599_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4594_);
                    crate::leanh::lean_dec(v_a_4590_);
                    v_val_4600_ = crate::leanh::lean_ctor_get(v_fst_4594_, 0);
                    crate::leanh::lean_inc(v_val_4600_);
                    crate::leanh::lean_dec_ref_known(v_fst_4594_, 1);
                    if v_isShared_4593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4592_, 0, v_val_4600_);
                        v___x_4602_ = v___x_4592_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_val_4600_);
                        v___x_4602_ = v_reuseFailAlloc_4603_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4598_;
            }
            8 => {
                return v___x_4602_;
            }
            9 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(
    mut v_init_4613_: *mut crate::leanh::LeanObject,
    mut v_as_4614_: *mut crate::leanh::LeanObject,
    mut v_sz_4615_: usize,
    mut v_i_4616_: usize,
    mut v_b_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v_a_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4632_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: usize = 0;
    let mut v___x_4645_: usize = 0;
    let mut v_reuseFailAlloc_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v_a_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_unused_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4621_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
                if v___x_4621_ == 0 {
                    v___x_4622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4622_, 0, v_b_4617_);
                    return v___x_4622_;
                } else {
                    v_snd_4623_ = crate::leanh::lean_ctor_get(v_b_4617_, 1);
                    v_isSharedCheck_4657_ = (!crate::leanh::lean_is_exclusive(v_b_4617_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v_unused_4658_ = crate::leanh::lean_ctor_get(v_b_4617_, 0);
                        crate::leanh::lean_dec(v_unused_4658_);
                        v___x_4625_ = v_b_4617_;
                        v_isShared_4626_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4623_);
                        crate::leanh::lean_dec(v_b_4617_);
                        v___x_4625_ = crate::leanh::lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4627_ = lean_array_uget_borrowed(v_as_4614_, v_i_4616_);
                crate::leanh::lean_inc(v_snd_4623_);
                v___x_4628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4613_, v_a_4627_, v_snd_4623_, v___y_4618_, v___y_4619_);
                if crate::leanh::lean_obj_tag(v___x_4628_) == 0 {
                    v_a_4629_ = crate::leanh::lean_ctor_get(v___x_4628_, 0);
                    v_isSharedCheck_4648_ = (!crate::leanh::lean_is_exclusive(v___x_4628_)) as u8;
                    if v_isSharedCheck_4648_ == 0 {
                        v___x_4631_ = v___x_4628_;
                        v_isShared_4632_ = v_isSharedCheck_4648_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4629_);
                        crate::leanh::lean_dec(v___x_4628_);
                        v___x_4631_ = crate::leanh::lean_box(0);
                        v_isShared_4632_ = v_isSharedCheck_4648_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4625_);
                    crate::leanh::lean_dec(v_snd_4623_);
                    v_a_4649_ = crate::leanh::lean_ctor_get(v___x_4628_, 0);
                    v_isSharedCheck_4656_ = (!crate::leanh::lean_is_exclusive(v___x_4628_)) as u8;
                    if v_isSharedCheck_4656_ == 0 {
                        v___x_4651_ = v___x_4628_;
                        v_isShared_4652_ = v_isSharedCheck_4656_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4649_);
                        crate::leanh::lean_dec(v___x_4628_);
                        v___x_4651_ = crate::leanh::lean_box(0);
                        v_isShared_4652_ = v_isSharedCheck_4656_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4629_) == 0 {
                    v___x_4633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4633_, 0, v_a_4629_);
                    if v_isShared_4626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4633_);
                        v___x_4635_ = v___x_4625_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4639_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_snd_4623_);
                        v___x_4635_ = v_reuseFailAlloc_4639_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4631_);
                    crate::leanh::lean_dec(v_snd_4623_);
                    v_a_4640_ = crate::leanh::lean_ctor_get(v_a_4629_, 0);
                    crate::leanh::lean_inc(v_a_4640_);
                    crate::leanh::lean_dec_ref_known(v_a_4629_, 1);
                    v___x_4641_ = crate::leanh::lean_box(0);
                    if v_isShared_4626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4625_, 1, v_a_4640_);
                        crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4641_);
                        v___x_4643_ = v___x_4625_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4641_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_a_4640_);
                        v___x_4643_ = v_reuseFailAlloc_4647_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4632_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4631_, 0, v___x_4635_);
                    v___x_4637_ = v___x_4631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
                    v___x_4637_ = v_reuseFailAlloc_4638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4637_;
            }
            5 => {
                v___x_4644_ = 1usize;
                v___x_4645_ = lean_usize_add(v_i_4616_, v___x_4644_);
                v_i_4616_ = v___x_4645_;
                v_b_4617_ = v___x_4643_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4652_ == 0 {
                    v___x_4654_ = v___x_4651_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9___boxed(
    mut v_init_4659_: *mut crate::leanh::LeanObject,
    mut v_as_4660_: *mut crate::leanh::LeanObject,
    mut v_sz_4661_: *mut crate::leanh::LeanObject,
    mut v_i_4662_: *mut crate::leanh::LeanObject,
    mut v_b_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4667_: usize = 0;
    let mut v_i_boxed_4668_: usize = 0;
    let mut v_res_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4667_ = crate::leanh::lean_unbox_usize(v_sz_4661_);
    crate::leanh::lean_dec(v_sz_4661_);
    v_i_boxed_4668_ = crate::leanh::lean_unbox_usize(v_i_4662_);
    crate::leanh::lean_dec(v_i_4662_);
    v_res_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_4659_, v_as_4660_, v_sz_boxed_4667_, v_i_boxed_4668_, v_b_4663_, v___y_4664_, v___y_4665_);
    crate::leanh::lean_dec(v___y_4665_);
    crate::leanh::lean_dec_ref(v___y_4664_);
    crate::leanh::lean_dec_ref(v_as_4660_);
    return v_res_4669_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(
    mut v_init_4670_: *mut crate::leanh::LeanObject,
    mut v_n_4671_: *mut crate::leanh::LeanObject,
    mut v_b_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4670_, v_n_4671_, v_b_4672_, v___y_4673_, v___y_4674_);
    crate::leanh::lean_dec(v___y_4674_);
    crate::leanh::lean_dec_ref(v___y_4673_);
    crate::leanh::lean_dec_ref(v_n_4671_);
    return v_res_4676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(
    mut v_as_4680_: *mut crate::leanh::LeanObject,
    mut v_sz_4681_: usize,
    mut v_i_4682_: usize,
    mut v_b_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: usize = 0;
    let mut v___x_4699_: usize = 0;
    let mut v_a_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut v_a_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4716_: u8 = 0;
    let mut v_a_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4687_ = lean_usize_dec_lt(v_i_4682_, v_sz_4681_);
                if v___x_4687_ == 0 {
                    v___x_4688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4688_, 0, v_b_4683_);
                    return v___x_4688_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4683_);
                    v___x_4689_ = crate::leanh::lean_box(0);
                    v_a_4690_ = lean_array_uget_borrowed(v_as_4680_, v_i_4682_);
                    crate::leanh::lean_inc(v_a_4690_);
                    v___x_4691_ = l_Lean_Linter_List_numericalIndices(v_a_4690_);
                    v___x_4692_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4691_, v___x_4689_, v___y_4684_, v___y_4685_);
                    crate::leanh::lean_dec(v___x_4691_);
                    if crate::leanh::lean_obj_tag(v___x_4692_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4692_, 1);
                        crate::leanh::lean_inc(v_a_4690_);
                        v___x_4693_ = l_Lean_Linter_List_numericalWidths(v_a_4690_);
                        v___x_4694_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4693_, v___x_4689_, v___y_4684_, v___y_4685_);
                        crate::leanh::lean_dec(v___x_4693_);
                        if crate::leanh::lean_obj_tag(v___x_4694_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4694_, 1);
                            crate::leanh::lean_inc(v_a_4690_);
                            v___x_4695_ = l_Lean_Linter_List_bitVecWidths(v_a_4690_);
                            v___x_4696_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4695_, v___x_4689_, v___y_4684_, v___y_4685_);
                            crate::leanh::lean_dec(v___x_4695_);
                            if crate::leanh::lean_obj_tag(v___x_4696_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4696_, 1);
                                v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                v___x_4698_ = 1usize;
                                v___x_4699_ = lean_usize_add(v_i_4682_, v___x_4698_);
                                v_i_4682_ = v___x_4699_;
                                v_b_4683_ = v___x_4697_;
                                state = 0;
                                continue;
                            } else {
                                v_a_4701_ = crate::leanh::lean_ctor_get(v___x_4696_, 0);
                                v_isSharedCheck_4708_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4696_)) as u8;
                                if v_isSharedCheck_4708_ == 0 {
                                    v___x_4703_ = v___x_4696_;
                                    v_isShared_4704_ = v_isSharedCheck_4708_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4701_);
                                    crate::leanh::lean_dec(v___x_4696_);
                                    v___x_4703_ = crate::leanh::lean_box(0);
                                    v_isShared_4704_ = v_isSharedCheck_4708_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4709_ = crate::leanh::lean_ctor_get(v___x_4694_, 0);
                            v_isSharedCheck_4716_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4694_)) as u8;
                            if v_isSharedCheck_4716_ == 0 {
                                v___x_4711_ = v___x_4694_;
                                v_isShared_4712_ = v_isSharedCheck_4716_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4709_);
                                crate::leanh::lean_dec(v___x_4694_);
                                v___x_4711_ = crate::leanh::lean_box(0);
                                v_isShared_4712_ = v_isSharedCheck_4716_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4717_ = crate::leanh::lean_ctor_get(v___x_4692_, 0);
                        v_isSharedCheck_4724_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4692_)) as u8;
                        if v_isSharedCheck_4724_ == 0 {
                            v___x_4719_ = v___x_4692_;
                            v_isShared_4720_ = v_isSharedCheck_4724_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4717_);
                            crate::leanh::lean_dec(v___x_4692_);
                            v___x_4719_ = crate::leanh::lean_box(0);
                            v_isShared_4720_ = v_isSharedCheck_4724_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4704_ == 0 {
                    v___x_4706_ = v___x_4703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
                    v___x_4706_ = v_reuseFailAlloc_4707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4706_;
            }
            3 => {
                if v_isShared_4712_ == 0 {
                    v___x_4714_ = v___x_4711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
                    v___x_4714_ = v_reuseFailAlloc_4715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4714_;
            }
            5 => {
                if v_isShared_4720_ == 0 {
                    v___x_4722_ = v___x_4719_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
                    v___x_4722_ = v_reuseFailAlloc_4723_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___boxed(
    mut v_as_4725_: *mut crate::leanh::LeanObject,
    mut v_sz_4726_: *mut crate::leanh::LeanObject,
    mut v_i_4727_: *mut crate::leanh::LeanObject,
    mut v_b_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4732_: usize = 0;
    let mut v_i_boxed_4733_: usize = 0;
    let mut v_res_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4732_ = crate::leanh::lean_unbox_usize(v_sz_4726_);
    crate::leanh::lean_dec(v_sz_4726_);
    v_i_boxed_4733_ = crate::leanh::lean_unbox_usize(v_i_4727_);
    crate::leanh::lean_dec(v_i_4727_);
    v_res_4734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_4725_, v_sz_boxed_4732_, v_i_boxed_4733_, v_b_4728_, v___y_4729_, v___y_4730_);
    crate::leanh::lean_dec(v___y_4730_);
    crate::leanh::lean_dec_ref(v___y_4729_);
    crate::leanh::lean_dec_ref(v_as_4725_);
    return v_res_4734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(
    mut v_as_4735_: *mut crate::leanh::LeanObject,
    mut v_sz_4736_: usize,
    mut v_i_4737_: usize,
    mut v_b_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4742_: u8 = 0;
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_a_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut v_a_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4775_: u8 = 0;
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = lean_usize_dec_lt(v_i_4737_, v_sz_4736_);
                if v___x_4742_ == 0 {
                    v___x_4743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4743_, 0, v_b_4738_);
                    return v___x_4743_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4738_);
                    v___x_4744_ = crate::leanh::lean_box(0);
                    v_a_4745_ = lean_array_uget_borrowed(v_as_4735_, v_i_4737_);
                    crate::leanh::lean_inc(v_a_4745_);
                    v___x_4746_ = l_Lean_Linter_List_numericalIndices(v_a_4745_);
                    v___x_4747_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4746_, v___x_4744_, v___y_4739_, v___y_4740_);
                    crate::leanh::lean_dec(v___x_4746_);
                    if crate::leanh::lean_obj_tag(v___x_4747_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4747_, 1);
                        crate::leanh::lean_inc(v_a_4745_);
                        v___x_4748_ = l_Lean_Linter_List_numericalWidths(v_a_4745_);
                        v___x_4749_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4748_, v___x_4744_, v___y_4739_, v___y_4740_);
                        crate::leanh::lean_dec(v___x_4748_);
                        if crate::leanh::lean_obj_tag(v___x_4749_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4749_, 1);
                            crate::leanh::lean_inc(v_a_4745_);
                            v___x_4750_ = l_Lean_Linter_List_bitVecWidths(v_a_4745_);
                            v___x_4751_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4750_, v___x_4744_, v___y_4739_, v___y_4740_);
                            crate::leanh::lean_dec(v___x_4750_);
                            if crate::leanh::lean_obj_tag(v___x_4751_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4751_, 1);
                                v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                v___x_4753_ = 1usize;
                                v___x_4754_ = lean_usize_add(v_i_4737_, v___x_4753_);
                                v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_4735_, v_sz_4736_, v___x_4754_, v___x_4752_, v___y_4739_, v___y_4740_);
                                return v___x_4755_;
                            } else {
                                v_a_4756_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                                v_isSharedCheck_4763_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4751_)) as u8;
                                if v_isSharedCheck_4763_ == 0 {
                                    v___x_4758_ = v___x_4751_;
                                    v_isShared_4759_ = v_isSharedCheck_4763_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4756_);
                                    crate::leanh::lean_dec(v___x_4751_);
                                    v___x_4758_ = crate::leanh::lean_box(0);
                                    v_isShared_4759_ = v_isSharedCheck_4763_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4764_ = crate::leanh::lean_ctor_get(v___x_4749_, 0);
                            v_isSharedCheck_4771_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4749_)) as u8;
                            if v_isSharedCheck_4771_ == 0 {
                                v___x_4766_ = v___x_4749_;
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4764_);
                                crate::leanh::lean_dec(v___x_4749_);
                                v___x_4766_ = crate::leanh::lean_box(0);
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4772_ = crate::leanh::lean_ctor_get(v___x_4747_, 0);
                        v_isSharedCheck_4779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4747_)) as u8;
                        if v_isSharedCheck_4779_ == 0 {
                            v___x_4774_ = v___x_4747_;
                            v_isShared_4775_ = v_isSharedCheck_4779_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4772_);
                            crate::leanh::lean_dec(v___x_4747_);
                            v___x_4774_ = crate::leanh::lean_box(0);
                            v_isShared_4775_ = v_isSharedCheck_4779_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4759_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4761_;
            }
            3 => {
                if v_isShared_4767_ == 0 {
                    v___x_4769_ = v___x_4766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
                    v___x_4769_ = v_reuseFailAlloc_4770_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4769_;
            }
            5 => {
                if v_isShared_4775_ == 0 {
                    v___x_4777_ = v___x_4774_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
                    v___x_4777_ = v_reuseFailAlloc_4778_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8___boxed(
    mut v_as_4780_: *mut crate::leanh::LeanObject,
    mut v_sz_4781_: *mut crate::leanh::LeanObject,
    mut v_i_4782_: *mut crate::leanh::LeanObject,
    mut v_b_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4787_: usize = 0;
    let mut v_i_boxed_4788_: usize = 0;
    let mut v_res_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4787_ = crate::leanh::lean_unbox_usize(v_sz_4781_);
    crate::leanh::lean_dec(v_sz_4781_);
    v_i_boxed_4788_ = crate::leanh::lean_unbox_usize(v_i_4782_);
    crate::leanh::lean_dec(v_i_4782_);
    v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_4780_, v_sz_boxed_4787_, v_i_boxed_4788_, v_b_4783_, v___y_4784_, v___y_4785_);
    crate::leanh::lean_dec(v___y_4785_);
    crate::leanh::lean_dec_ref(v___y_4784_);
    crate::leanh::lean_dec_ref(v_as_4780_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(
    mut v_t_4790_: *mut crate::leanh::LeanObject,
    mut v_init_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v_a_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4809_: usize = 0;
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4815_: u8 = 0;
    let mut v_fst_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v_a_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v_a_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4795_ = crate::leanh::lean_ctor_get(v_t_4790_, 0);
                v_tail_4796_ = crate::leanh::lean_ctor_get(v_t_4790_, 1);
                v___x_4797_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4791_, v_root_4795_, v_init_4791_, v___y_4792_, v___y_4793_);
                if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4834_ = (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4834_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_dec(v___x_4797_);
                        v___x_4800_ = crate::leanh::lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4835_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4842_ = (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4837_ = v___x_4797_;
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4835_);
                        crate::leanh::lean_dec(v___x_4797_);
                        v___x_4837_ = crate::leanh::lean_box(0);
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4798_) == 0 {
                    v_a_4802_ = crate::leanh::lean_ctor_get(v_a_4798_, 0);
                    crate::leanh::lean_inc(v_a_4802_);
                    crate::leanh::lean_dec_ref_known(v_a_4798_, 1);
                    if v_isShared_4801_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4800_, 0, v_a_4802_);
                        v___x_4804_ = v___x_4800_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4802_);
                        v___x_4804_ = v_reuseFailAlloc_4805_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4800_);
                    v_a_4806_ = crate::leanh::lean_ctor_get(v_a_4798_, 0);
                    crate::leanh::lean_inc(v_a_4806_);
                    crate::leanh::lean_dec_ref_known(v_a_4798_, 1);
                    v___x_4807_ = crate::leanh::lean_box(0);
                    v___x_4808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4808_, 0, v___x_4807_);
                    crate::leanh::lean_ctor_set(v___x_4808_, 1, v_a_4806_);
                    v_sz_4809_ = lean_array_size(v_tail_4796_);
                    v___x_4810_ = 0usize;
                    v___x_4811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_4796_, v_sz_4809_, v___x_4810_, v___x_4808_, v___y_4792_, v___y_4793_);
                    if crate::leanh::lean_obj_tag(v___x_4811_) == 0 {
                        v_a_4812_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                        v_isSharedCheck_4825_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                        if v_isSharedCheck_4825_ == 0 {
                            v___x_4814_ = v___x_4811_;
                            v_isShared_4815_ = v_isSharedCheck_4825_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4812_);
                            crate::leanh::lean_dec(v___x_4811_);
                            v___x_4814_ = crate::leanh::lean_box(0);
                            v_isShared_4815_ = v_isSharedCheck_4825_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4826_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                        v_isSharedCheck_4833_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                        if v_isSharedCheck_4833_ == 0 {
                            v___x_4828_ = v___x_4811_;
                            v_isShared_4829_ = v_isSharedCheck_4833_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4826_);
                            crate::leanh::lean_dec(v___x_4811_);
                            v___x_4828_ = crate::leanh::lean_box(0);
                            v_isShared_4829_ = v_isSharedCheck_4833_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4804_;
            }
            3 => {
                v_fst_4816_ = crate::leanh::lean_ctor_get(v_a_4812_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4816_) == 0 {
                    v_snd_4817_ = crate::leanh::lean_ctor_get(v_a_4812_, 1);
                    crate::leanh::lean_inc(v_snd_4817_);
                    crate::leanh::lean_dec(v_a_4812_);
                    if v_isShared_4815_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4814_, 0, v_snd_4817_);
                        v___x_4819_ = v___x_4814_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_snd_4817_);
                        v___x_4819_ = v_reuseFailAlloc_4820_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4816_);
                    crate::leanh::lean_dec(v_a_4812_);
                    v_val_4821_ = crate::leanh::lean_ctor_get(v_fst_4816_, 0);
                    crate::leanh::lean_inc(v_val_4821_);
                    crate::leanh::lean_dec_ref_known(v_fst_4816_, 1);
                    if v_isShared_4815_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4814_, 0, v_val_4821_);
                        v___x_4823_ = v___x_4814_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4824_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_val_4821_);
                        v___x_4823_ = v_reuseFailAlloc_4824_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4819_;
            }
            5 => {
                return v___x_4823_;
            }
            6 => {
                if v_isShared_4829_ == 0 {
                    v___x_4831_ = v___x_4828_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
                    v___x_4831_ = v_reuseFailAlloc_4832_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4831_;
            }
            8 => {
                if v_isShared_4838_ == 0 {
                    v___x_4840_ = v___x_4837_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
                    v___x_4840_ = v_reuseFailAlloc_4841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6___boxed(
    mut v_t_4843_: *mut crate::leanh::LeanObject,
    mut v_init_4844_: *mut crate::leanh::LeanObject,
    mut v___y_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4848_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(
        v_t_4843_,
        v_init_4844_,
        v___y_4845_,
        v___y_4846_,
    );
    crate::leanh::lean_dec(v___y_4846_);
    crate::leanh::lean_dec_ref(v___y_4845_);
    crate::leanh::lean_dec_ref(v_t_4843_);
    return v_res_4848_;
}
pub unsafe fn l_Lean_Linter_List_indexLinter___lam__0(
    mut v_stx_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
    mut v___y_4851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v_v_4869_: u8 = 0;
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4891_: u8 = 0;
    let mut v_unused_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4853_ = lean_st_ref_get(v___y_4851_);
                v_scopes_4857_ = crate::leanh::lean_ctor_get(v___x_4853_, 2);
                crate::leanh::lean_inc(v_scopes_4857_);
                crate::leanh::lean_dec(v___x_4853_);
                v___x_4858_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_4859_ = l_List_head_x21___redArg(v___x_4858_, v_scopes_4857_);
                crate::leanh::lean_dec(v_scopes_4857_);
                v_opts_4860_ = crate::leanh::lean_ctor_get(v___x_4859_, 1);
                crate::leanh::lean_inc_ref(v_opts_4860_);
                crate::leanh::lean_dec(v___x_4859_);
                v___x_4861_ = l_Lean_Linter_List_linter_indexVariables;
                v_name_4862_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                v_map_4863_ = crate::leanh::lean_ctor_get(v_opts_4860_, 0);
                crate::leanh::lean_inc(v_map_4863_);
                crate::leanh::lean_dec_ref(v_opts_4860_);
                v___x_4864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4863_, v_name_4862_);
                crate::leanh::lean_dec(v_map_4863_);
                if crate::leanh::lean_obj_tag(v___x_4864_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4865_ = crate::leanh::lean_ctor_get(v___x_4864_, 0);
                    v_isSharedCheck_4897_ = (!crate::leanh::lean_is_exclusive(v___x_4864_)) as u8;
                    if v_isSharedCheck_4897_ == 0 {
                        v___x_4867_ = v___x_4864_;
                        v_isShared_4868_ = v_isSharedCheck_4897_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4865_);
                        crate::leanh::lean_dec(v___x_4864_);
                        v___x_4867_ = crate::leanh::lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4897_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4855_ = crate::leanh::lean_box(0);
                v___x_4856_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4856_, 0, v___x_4855_);
                return v___x_4856_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_4865_) == 1 {
                    v_v_4869_ = crate::leanh::lean_ctor_get_uint8(v_val_4865_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_val_4865_, 0);
                    if v_v_4869_ == 0 {
                        crate::leanh::lean_del_object(v___x_4867_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4870_ = lean_st_ref_get(v___y_4851_);
                        v_messages_4871_ = crate::leanh::lean_ctor_get(v___x_4870_, 1);
                        crate::leanh::lean_inc_ref(v_messages_4871_);
                        crate::leanh::lean_dec(v___x_4870_);
                        v___x_4872_ = l_Lean_MessageLog_hasErrors(v_messages_4871_);
                        crate::leanh::lean_dec_ref(v_messages_4871_);
                        if v___x_4872_ == 0 {
                            v___x_4873_ = lean_st_ref_get(v___y_4851_);
                            v_infoState_4879_ = crate::leanh::lean_ctor_get(v___x_4873_, 8);
                            crate::leanh::lean_inc_ref(v_infoState_4879_);
                            crate::leanh::lean_dec(v___x_4873_);
                            v_enabled_4880_ = crate::leanh::lean_ctor_get_uint8(
                                v_infoState_4879_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            );
                            crate::leanh::lean_dec_ref(v_infoState_4879_);
                            if v_enabled_4880_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_4872_ == 0 {
                                    crate::leanh::lean_del_object(v___x_4867_);
                                    v___x_4881_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_4851_);
                                    v_a_4882_ = crate::leanh::lean_ctor_get(v___x_4881_, 0);
                                    crate::leanh::lean_inc(v_a_4882_);
                                    crate::leanh::lean_dec_ref(v___x_4881_);
                                    v___x_4883_ = crate::leanh::lean_box(0);
                                    v___x_4884_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_4882_, v___x_4883_, v___y_4850_, v___y_4851_);
                                    crate::leanh::lean_dec(v_a_4882_);
                                    if crate::leanh::lean_obj_tag(v___x_4884_) == 0 {
                                        v_isSharedCheck_4891_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4884_)) as u8;
                                        if v_isSharedCheck_4891_ == 0 {
                                            v_unused_4892_ =
                                                crate::leanh::lean_ctor_get(v___x_4884_, 0);
                                            crate::leanh::lean_dec(v_unused_4892_);
                                            v___x_4886_ = v___x_4884_;
                                            v_isShared_4887_ = v_isSharedCheck_4891_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_4884_);
                                            v___x_4886_ = crate::leanh::lean_box(0);
                                            v_isShared_4887_ = v_isSharedCheck_4891_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        return v___x_4884_;
                                    }
                                } else {
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4893_ = crate::leanh::lean_box(0);
                            if v_isShared_4868_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4867_, 0);
                                crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4893_);
                                v___x_4895_ = v___x_4867_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4896_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
                                v___x_4895_ = v_reuseFailAlloc_4896_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4867_);
                    crate::leanh::lean_dec(v_val_4865_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4875_ = crate::leanh::lean_box(0);
                if v_isShared_4868_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4867_, 0);
                    crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4867_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4877_;
            }
            5 => {
                if v_isShared_4887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4886_, 0, v___x_4883_);
                    v___x_4889_ = v___x_4886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4883_);
                    v___x_4889_ = v_reuseFailAlloc_4890_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4889_;
            }
            7 => {
                return v___x_4895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_indexLinter___lam__0___boxed(
    mut v_stx_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4902_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_4898_, v___y_4899_, v___y_4900_);
    crate::leanh::lean_dec(v___y_4900_);
    crate::leanh::lean_dec_ref(v___y_4899_);
    crate::leanh::lean_dec(v_stx_4898_);
    return v_res_4902_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(
    mut v_as_4916_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4917_: *mut crate::leanh::LeanObject,
    mut v_b_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
        v_as_x27_4917_,
        v_b_4918_,
        v___y_4920_,
        v___y_4921_,
    );
    return v___x_4923_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(
    mut v_as_4924_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4925_: *mut crate::leanh::LeanObject,
    mut v_b_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4931_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(
        v_as_4924_,
        v_as_x27_4925_,
        v_b_4926_,
        v_a_4927_,
        v___y_4928_,
        v___y_4929_,
    );
    crate::leanh::lean_dec(v___y_4929_);
    crate::leanh::lean_dec_ref(v___y_4928_);
    crate::leanh::lean_dec(v_as_x27_4925_);
    crate::leanh::lean_dec(v_as_4924_);
    return v_res_4931_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(
    mut v_as_4932_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4933_: *mut crate::leanh::LeanObject,
    mut v_b_4934_: *mut crate::leanh::LeanObject,
    mut v_a_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
        v_as_x27_4933_,
        v_b_4934_,
        v___y_4936_,
        v___y_4937_,
    );
    return v___x_4939_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(
    mut v_as_4940_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4941_: *mut crate::leanh::LeanObject,
    mut v_b_4942_: *mut crate::leanh::LeanObject,
    mut v_a_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
    mut v___y_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(
        v_as_4940_,
        v_as_x27_4941_,
        v_b_4942_,
        v_a_4943_,
        v___y_4944_,
        v___y_4945_,
    );
    crate::leanh::lean_dec(v___y_4945_);
    crate::leanh::lean_dec_ref(v___y_4944_);
    crate::leanh::lean_dec(v_as_x27_4941_);
    crate::leanh::lean_dec(v_as_4940_);
    return v_res_4947_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(
    mut v_as_4948_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4949_: *mut crate::leanh::LeanObject,
    mut v_b_4950_: *mut crate::leanh::LeanObject,
    mut v_a_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
        v_as_x27_4949_,
        v_b_4950_,
        v___y_4952_,
        v___y_4953_,
    );
    return v___x_4955_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(
    mut v_as_4956_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4957_: *mut crate::leanh::LeanObject,
    mut v_b_4958_: *mut crate::leanh::LeanObject,
    mut v_a_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(
        v_as_4956_,
        v_as_x27_4957_,
        v_b_4958_,
        v_a_4959_,
        v___y_4960_,
        v___y_4961_,
    );
    crate::leanh::lean_dec(v___y_4961_);
    crate::leanh::lean_dec_ref(v___y_4960_);
    crate::leanh::lean_dec(v_as_x27_4957_);
    crate::leanh::lean_dec(v_as_4956_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(
    mut v_msgData_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4968_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_4964_, v___y_4966_);
    return v___x_4968_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(
    mut v_msgData_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
    mut v___y_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4973_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_4969_, v___y_4970_, v___y_4971_);
    crate::leanh::lean_dec(v___y_4971_);
    crate::leanh::lean_dec_ref(v___y_4970_);
    return v_res_4973_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4975_ = l_Lean_Linter_List_indexLinter;
    v___x_4976_ = l_Lean_Elab_Command_addLinter(v___x_4975_);
    return v___x_4976_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(
    mut v_a_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4978_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
    return v_res_4978_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
    mut v_e_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5040_: u8 = 0;
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_unused_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5040_ = l_Lean_Expr_hasMVar(v_e_5037_);
                if v___x_5040_ == 0 {
                    v___x_5041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5041_, 0, v_e_5037_);
                    return v___x_5041_;
                } else {
                    v___x_5042_ = lean_st_ref_get(v___y_5038_);
                    v_mctx_5043_ = crate::leanh::lean_ctor_get(v___x_5042_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5043_);
                    crate::leanh::lean_dec(v___x_5042_);
                    v___x_5044_ = l_Lean_instantiateMVarsCore(v_mctx_5043_, v_e_5037_);
                    v_fst_5045_ = crate::leanh::lean_ctor_get(v___x_5044_, 0);
                    crate::leanh::lean_inc(v_fst_5045_);
                    v_snd_5046_ = crate::leanh::lean_ctor_get(v___x_5044_, 1);
                    crate::leanh::lean_inc(v_snd_5046_);
                    crate::leanh::lean_dec_ref(v___x_5044_);
                    v___x_5047_ = lean_st_ref_take(v___y_5038_);
                    v_cache_5048_ = crate::leanh::lean_ctor_get(v___x_5047_, 1);
                    v_zetaDeltaFVarIds_5049_ = crate::leanh::lean_ctor_get(v___x_5047_, 2);
                    v_postponed_5050_ = crate::leanh::lean_ctor_get(v___x_5047_, 3);
                    v_diag_5051_ = crate::leanh::lean_ctor_get(v___x_5047_, 4);
                    v_isSharedCheck_5060_ = (!crate::leanh::lean_is_exclusive(v___x_5047_)) as u8;
                    if v_isSharedCheck_5060_ == 0 {
                        v_unused_5061_ = crate::leanh::lean_ctor_get(v___x_5047_, 0);
                        crate::leanh::lean_dec(v_unused_5061_);
                        v___x_5053_ = v___x_5047_;
                        v_isShared_5054_ = v_isSharedCheck_5060_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5051_);
                        crate::leanh::lean_inc(v_postponed_5050_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5049_);
                        crate::leanh::lean_inc(v_cache_5048_);
                        crate::leanh::lean_dec(v___x_5047_);
                        v___x_5053_ = crate::leanh::lean_box(0);
                        v_isShared_5054_ = v_isSharedCheck_5060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5053_, 0, v_snd_5046_);
                    v___x_5056_ = v___x_5053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5059_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_snd_5046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_cache_5048_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5059_,
                        2,
                        v_zetaDeltaFVarIds_5049_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 3, v_postponed_5050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 4, v_diag_5051_);
                    v___x_5056_ = v_reuseFailAlloc_5059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5057_ = lean_st_ref_set(v___y_5038_, v___x_5056_);
                v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5058_, 0, v_fst_5045_);
                return v___x_5058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(
    mut v_e_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5065_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
        v_e_5062_,
        v___y_5063_,
    );
    crate::leanh::lean_dec(v___y_5063_);
    return v_res_5065_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(
    mut v_e_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5072_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
        v_e_5066_,
        v___y_5068_,
    );
    return v___x_5072_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(
    mut v_e_5073_: *mut crate::leanh::LeanObject,
    mut v___y_5074_: *mut crate::leanh::LeanObject,
    mut v___y_5075_: *mut crate::leanh::LeanObject,
    mut v___y_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(
        v_e_5073_,
        v___y_5074_,
        v___y_5075_,
        v___y_5076_,
        v___y_5077_,
    );
    crate::leanh::lean_dec(v___y_5077_);
    crate::leanh::lean_dec_ref(v___y_5076_);
    crate::leanh::lean_dec(v___y_5075_);
    crate::leanh::lean_dec_ref(v___y_5074_);
    return v_res_5079_;
}
pub unsafe fn _init_l_Lean_Linter_List_binders___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5083_ = crate::leanh::lean_box(0);
    v___x_5084_ = l_Lean_Linter_List_binders___lam__0___closed__1;
    v___x_5085_ = l_Lean_Expr_const___override(v___x_5084_, v___x_5083_);
    return v___x_5085_;
}
pub unsafe fn l_Lean_Linter_List_binders___lam__0(
    mut v_expr_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: u8 = 0;
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5112_: u8 = 0;
    let mut v___x_5113_: u8 = 0;
    let mut v___x_5114_: u8 = 0;
    let mut v_a_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5118_: u8 = 0;
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5096_ = l_Lean_Meta_saveState___redArg(v___y_5088_, v___y_5090_);
                if crate::leanh::lean_obj_tag(v___x_5096_) == 0 {
                    v_a_5097_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                    crate::leanh::lean_inc(v_a_5097_);
                    crate::leanh::lean_dec_ref_known(v___x_5096_, 1);
                    crate::leanh::lean_inc(v___y_5090_);
                    crate::leanh::lean_inc(v___y_5088_);
                    v___x_5098_ = lean_infer_type(
                        v_expr_5086_,
                        v___y_5087_,
                        v___y_5088_,
                        v___y_5089_,
                        v___y_5090_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5098_) == 0 {
                        crate::leanh::lean_dec(v_a_5097_);
                        crate::leanh::lean_dec(v___y_5090_);
                        v___y_5093_ = v___x_5098_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5099_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                        crate::leanh::lean_inc(v_a_5099_);
                        v___x_5113_ = l_Lean_Exception_isInterrupt(v_a_5099_);
                        if v___x_5113_ == 0 {
                            v___x_5114_ = l_Lean_Exception_isRuntime(v_a_5099_);
                            v___y_5101_ = v___x_5114_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_5099_);
                            v___y_5101_ = v___x_5113_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5090_);
                    crate::leanh::lean_dec_ref(v___y_5089_);
                    crate::leanh::lean_dec(v___y_5088_);
                    crate::leanh::lean_dec_ref(v___y_5087_);
                    crate::leanh::lean_dec_ref(v_expr_5086_);
                    v_a_5115_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                    v_isSharedCheck_5122_ = (!crate::leanh::lean_is_exclusive(v___x_5096_)) as u8;
                    if v_isSharedCheck_5122_ == 0 {
                        v___x_5117_ = v___x_5096_;
                        v_isShared_5118_ = v_isSharedCheck_5122_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5115_);
                        crate::leanh::lean_dec(v___x_5096_);
                        v___x_5117_ = crate::leanh::lean_box(0);
                        v_isShared_5118_ = v_isSharedCheck_5122_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5093_) == 0 {
                    v_a_5094_ = crate::leanh::lean_ctor_get(v___y_5093_, 0);
                    crate::leanh::lean_inc(v_a_5094_);
                    crate::leanh::lean_dec_ref_known(v___y_5093_, 1);
                    v___x_5095_ =
                        l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
                            v_a_5094_,
                            v___y_5088_,
                        );
                    crate::leanh::lean_dec(v___y_5088_);
                    return v___x_5095_;
                } else {
                    crate::leanh::lean_dec(v___y_5088_);
                    return v___y_5093_;
                }
            }
            2 => {
                if v___y_5101_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5098_, 1);
                    v___x_5102_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_5097_,
                        v___y_5088_,
                        v___y_5090_,
                    );
                    crate::leanh::lean_dec(v___y_5090_);
                    crate::leanh::lean_dec(v_a_5097_);
                    if crate::leanh::lean_obj_tag(v___x_5102_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5102_, 1);
                        v___x_5103_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_List_binders___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_List_binders___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Linter_List_binders___lam__0___closed__2,
                        );
                        v___x_5104_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_5103_, v___y_5088_);
                        crate::leanh::lean_dec(v___y_5088_);
                        return v___x_5104_;
                    } else {
                        crate::leanh::lean_dec(v___y_5088_);
                        v_a_5105_ = crate::leanh::lean_ctor_get(v___x_5102_, 0);
                        v_isSharedCheck_5112_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5102_)) as u8;
                        if v_isSharedCheck_5112_ == 0 {
                            v___x_5107_ = v___x_5102_;
                            v_isShared_5108_ = v_isSharedCheck_5112_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5105_);
                            crate::leanh::lean_dec(v___x_5102_);
                            v___x_5107_ = crate::leanh::lean_box(0);
                            v_isShared_5108_ = v_isSharedCheck_5112_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5097_);
                    crate::leanh::lean_dec(v___y_5090_);
                    v___y_5093_ = v___x_5098_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_5108_ == 0 {
                    v___x_5110_ = v___x_5107_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_a_5105_);
                    v___x_5110_ = v_reuseFailAlloc_5111_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5110_;
            }
            5 => {
                if v_isShared_5118_ == 0 {
                    v___x_5120_ = v___x_5117_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
                    v___x_5120_ = v_reuseFailAlloc_5121_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_binders___lam__0___boxed(
    mut v_expr_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Lean_Linter_List_binders___lam__0(
        v_expr_5123_,
        v___y_5124_,
        v___y_5125_,
        v___y_5126_,
        v___y_5127_,
    );
    return v_res_5129_;
}
pub unsafe fn l_Lean_Linter_List_binders___lam__1(
    mut v_p_5130_: *mut crate::leanh::LeanObject,
    mut v_ctx_5131_: *mut crate::leanh::LeanObject,
    mut v_ti_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isBinder_5134_: u8 = 0;
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5145_: u8 = 0;
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5162_: u8 = 0;
    let mut v_stx_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v_unused_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_a_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isBinder_5134_ = crate::leanh::lean_ctor_get_uint8(
                    v_ti_5132_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                if v_isBinder_5134_ == 0 {
                    crate::leanh::lean_dec_ref(v_ti_5132_);
                    crate::leanh::lean_dec_ref(v_ctx_5131_);
                    crate::leanh::lean_dec_ref(v_p_5130_);
                    v___x_5135_ = crate::leanh::lean_box(0);
                    v___x_5136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                } else {
                    v_toElabInfo_5137_ = crate::leanh::lean_ctor_get(v_ti_5132_, 0);
                    crate::leanh::lean_inc_ref(v_toElabInfo_5137_);
                    v_lctx_5138_ = crate::leanh::lean_ctor_get(v_ti_5132_, 1);
                    crate::leanh::lean_inc_ref_n(v_lctx_5138_, 2);
                    v_expr_5139_ = crate::leanh::lean_ctor_get(v_ti_5132_, 3);
                    crate::leanh::lean_inc_ref_n(v_expr_5139_, 2);
                    crate::leanh::lean_dec_ref(v_ti_5132_);
                    v___f_5140_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Linter_List_binders___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5140_, 0, v_expr_5139_);
                    v___x_5141_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_5131_,
                        v_lctx_5138_,
                        v___f_5140_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5141_) == 0 {
                        v_a_5142_ = crate::leanh::lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5144_ = v___x_5141_;
                            v_isShared_5145_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5142_);
                            crate::leanh::lean_dec(v___x_5141_);
                            v___x_5144_ = crate::leanh::lean_box(0);
                            v_isShared_5145_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expr_5139_);
                        crate::leanh::lean_dec_ref(v_lctx_5138_);
                        crate::leanh::lean_dec_ref(v_toElabInfo_5137_);
                        crate::leanh::lean_dec_ref(v_p_5130_);
                        v_a_5186_ = crate::leanh::lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5193_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5193_ == 0 {
                            v___x_5188_ = v___x_5141_;
                            v_isShared_5189_ = v_isSharedCheck_5193_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5186_);
                            crate::leanh::lean_dec(v___x_5141_);
                            v___x_5188_ = crate::leanh::lean_box(0);
                            v_isShared_5189_ = v_isSharedCheck_5193_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_5142_);
                v___x_5146_ = l_Lean_Expr_cleanupAnnotations(v_a_5142_);
                v___x_5147_ = crate::leanh::lean_apply_1(v_p_5130_, v___x_5146_);
                v___x_5148_ = (crate::leanh::lean_unbox(v___x_5147_) as u8);
                if v___x_5148_ == 0 {
                    crate::leanh::lean_dec(v_a_5142_);
                    crate::leanh::lean_dec_ref(v_expr_5139_);
                    crate::leanh::lean_dec_ref(v_lctx_5138_);
                    crate::leanh::lean_dec_ref(v_toElabInfo_5137_);
                    v___x_5149_ = crate::leanh::lean_box(0);
                    if v_isShared_5145_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5149_);
                        v___x_5151_ = v___x_5144_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
                        v___x_5151_ = v_reuseFailAlloc_5152_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_expr_5139_) == 1 {
                        v_fvarId_5153_ = crate::leanh::lean_ctor_get(v_expr_5139_, 0);
                        crate::leanh::lean_inc(v_fvarId_5153_);
                        crate::leanh::lean_dec_ref_known(v_expr_5139_, 1);
                        v___x_5154_ = lean_local_ctx_find(v_lctx_5138_, v_fvarId_5153_);
                        if crate::leanh::lean_obj_tag(v___x_5154_) == 0 {
                            crate::leanh::lean_dec(v_a_5142_);
                            crate::leanh::lean_dec_ref(v_toElabInfo_5137_);
                            v___x_5155_ = crate::leanh::lean_box(0);
                            if v_isShared_5145_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5155_);
                                v___x_5157_ = v___x_5144_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5158_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
                                v___x_5157_ = v_reuseFailAlloc_5158_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_val_5159_ = crate::leanh::lean_ctor_get(v___x_5154_, 0);
                            v_isSharedCheck_5180_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5154_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5161_ = v___x_5154_;
                                v_isShared_5162_ = v_isSharedCheck_5180_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5159_);
                                crate::leanh::lean_dec(v___x_5154_);
                                v___x_5161_ = crate::leanh::lean_box(0);
                                v_isShared_5162_ = v_isSharedCheck_5180_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5142_);
                        crate::leanh::lean_dec_ref(v_expr_5139_);
                        crate::leanh::lean_dec_ref(v_lctx_5138_);
                        crate::leanh::lean_dec_ref(v_toElabInfo_5137_);
                        v___x_5181_ = crate::leanh::lean_box(0);
                        if v_isShared_5145_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5181_);
                            v___x_5183_ = v___x_5144_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_5184_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                            v___x_5183_ = v_reuseFailAlloc_5184_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5151_;
            }
            3 => {
                return v___x_5157_;
            }
            4 => {
                v_stx_5163_ = crate::leanh::lean_ctor_get(v_toElabInfo_5137_, 1);
                v_isSharedCheck_5178_ =
                    (!crate::leanh::lean_is_exclusive(v_toElabInfo_5137_)) as u8;
                if v_isSharedCheck_5178_ == 0 {
                    v_unused_5179_ = crate::leanh::lean_ctor_get(v_toElabInfo_5137_, 0);
                    crate::leanh::lean_dec(v_unused_5179_);
                    v___x_5165_ = v_toElabInfo_5137_;
                    v_isShared_5166_ = v_isSharedCheck_5178_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stx_5163_);
                    crate::leanh::lean_dec(v_toElabInfo_5137_);
                    v___x_5165_ = crate::leanh::lean_box(0);
                    v_isShared_5166_ = v_isSharedCheck_5178_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5167_ = l_Lean_LocalDecl_userName(v_val_5159_);
                crate::leanh::lean_dec(v_val_5159_);
                if v_isShared_5166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5165_, 1, v_a_5142_);
                    crate::leanh::lean_ctor_set(v___x_5165_, 0, v___x_5167_);
                    v___x_5169_ = v___x_5165_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 1, v_a_5142_);
                    v___x_5169_ = v_reuseFailAlloc_5177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5170_, 0, v_stx_5163_);
                crate::leanh::lean_ctor_set(v___x_5170_, 1, v___x_5169_);
                if v_isShared_5162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5161_, 0, v___x_5170_);
                    v___x_5172_ = v___x_5161_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5170_);
                    v___x_5172_ = v_reuseFailAlloc_5176_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5172_);
                    v___x_5174_ = v___x_5144_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5174_;
            }
            9 => {
                return v___x_5183_;
            }
            10 => {
                if v_isShared_5189_ == 0 {
                    v___x_5191_ = v___x_5188_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
                    v___x_5191_ = v_reuseFailAlloc_5192_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_binders___lam__1___boxed(
    mut v_p_5194_: *mut crate::leanh::LeanObject,
    mut v_ctx_5195_: *mut crate::leanh::LeanObject,
    mut v_ti_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Linter_List_binders___lam__1(v_p_5194_, v_ctx_5195_, v_ti_5196_);
    return v_res_5198_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5199_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_5199_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(
    mut v_f_5200_: *mut crate::leanh::LeanObject,
    mut v___x_5201_: *mut crate::leanh::LeanObject,
    mut v_x_5202_: *mut crate::leanh::LeanObject,
    mut v_x_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: usize = 0;
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: usize = 0;
    let mut v___x_5223_: usize = 0;
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_vs_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: usize = 0;
    let mut v___x_5241_: usize = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: usize = 0;
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5202_) == 0 {
                    v_cs_5205_ = crate::leanh::lean_ctor_get(v_x_5202_, 0);
                    v_isSharedCheck_5225_ = (!crate::leanh::lean_is_exclusive(v_x_5202_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5207_ = v_x_5202_;
                        v_isShared_5208_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_5205_);
                        crate::leanh::lean_dec(v_x_5202_);
                        v___x_5207_ = crate::leanh::lean_box(0);
                        v_isShared_5208_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5226_ = crate::leanh::lean_ctor_get(v_x_5202_, 0);
                    v_isSharedCheck_5246_ = (!crate::leanh::lean_is_exclusive(v_x_5202_)) as u8;
                    if v_isSharedCheck_5246_ == 0 {
                        v___x_5228_ = v_x_5202_;
                        v_isShared_5229_ = v_isSharedCheck_5246_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5226_);
                        crate::leanh::lean_dec(v_x_5202_);
                        v___x_5228_ = crate::leanh::lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5246_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5209_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5210_ = lean_array_get_size(v_cs_5205_);
                v___x_5211_ = lean_nat_dec_lt(v___x_5209_, v___x_5210_);
                if v___x_5211_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_5205_);
                    crate::leanh::lean_dec(v___x_5201_);
                    crate::leanh::lean_dec_ref(v_f_5200_);
                    if v_isShared_5208_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5207_, 0, v_x_5203_);
                        v___x_5213_ = v___x_5207_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_x_5203_);
                        v___x_5213_ = v_reuseFailAlloc_5214_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5215_ = lean_nat_dec_le(v___x_5210_, v___x_5210_);
                    if v___x_5215_ == 0 {
                        if v___x_5211_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_5205_);
                            crate::leanh::lean_dec(v___x_5201_);
                            crate::leanh::lean_dec_ref(v_f_5200_);
                            if v_isShared_5208_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5207_, 0, v_x_5203_);
                                v___x_5217_ = v___x_5207_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5218_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_x_5203_);
                                v___x_5217_ = v_reuseFailAlloc_5218_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5207_);
                            v___x_5219_ = 0usize;
                            v___x_5220_ = lean_usize_of_nat(v___x_5210_);
                            v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5200_, v___x_5201_, v_cs_5205_, v___x_5219_, v___x_5220_, v_x_5203_);
                            crate::leanh::lean_dec_ref(v_cs_5205_);
                            return v___x_5221_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5207_);
                        v___x_5222_ = 0usize;
                        v___x_5223_ = lean_usize_of_nat(v___x_5210_);
                        v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5200_, v___x_5201_, v_cs_5205_, v___x_5222_, v___x_5223_, v_x_5203_);
                        crate::leanh::lean_dec_ref(v_cs_5205_);
                        return v___x_5224_;
                    }
                }
            }
            2 => {
                return v___x_5213_;
            }
            3 => {
                return v___x_5217_;
            }
            4 => {
                v___x_5230_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5231_ = lean_array_get_size(v_vs_5226_);
                v___x_5232_ = lean_nat_dec_lt(v___x_5230_, v___x_5231_);
                if v___x_5232_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_5226_);
                    crate::leanh::lean_dec(v___x_5201_);
                    crate::leanh::lean_dec_ref(v_f_5200_);
                    if v_isShared_5229_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5228_, 0);
                        crate::leanh::lean_ctor_set(v___x_5228_, 0, v_x_5203_);
                        v___x_5234_ = v___x_5228_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_x_5203_);
                        v___x_5234_ = v_reuseFailAlloc_5235_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_5236_ = lean_nat_dec_le(v___x_5231_, v___x_5231_);
                    if v___x_5236_ == 0 {
                        if v___x_5232_ == 0 {
                            crate::leanh::lean_dec_ref(v_vs_5226_);
                            crate::leanh::lean_dec(v___x_5201_);
                            crate::leanh::lean_dec_ref(v_f_5200_);
                            if v_isShared_5229_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_5228_, 0);
                                crate::leanh::lean_ctor_set(v___x_5228_, 0, v_x_5203_);
                                v___x_5238_ = v___x_5228_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_5239_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_x_5203_);
                                v___x_5238_ = v_reuseFailAlloc_5239_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5228_);
                            v___x_5240_ = 0usize;
                            v___x_5241_ = lean_usize_of_nat(v___x_5231_);
                            v___x_5242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5200_, v___x_5201_, v_vs_5226_, v___x_5240_, v___x_5241_, v_x_5203_);
                            crate::leanh::lean_dec_ref(v_vs_5226_);
                            return v___x_5242_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5228_);
                        v___x_5243_ = 0usize;
                        v___x_5244_ = lean_usize_of_nat(v___x_5231_);
                        v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5200_, v___x_5201_, v_vs_5226_, v___x_5243_, v___x_5244_, v_x_5203_);
                        crate::leanh::lean_dec_ref(v_vs_5226_);
                        return v___x_5245_;
                    }
                }
            }
            5 => {
                return v___x_5234_;
            }
            6 => {
                return v___x_5238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_f_5247_: *mut crate::leanh::LeanObject,
    mut v___x_5248_: *mut crate::leanh::LeanObject,
    mut v_as_5249_: *mut crate::leanh::LeanObject,
    mut v_i_5250_: usize,
    mut v_stop_5251_: usize,
    mut v_b_5252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: usize = 0;
    let mut v___x_5259_: usize = 0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5254_ = lean_usize_dec_eq(v_i_5250_, v_stop_5251_);
                if v___x_5254_ == 0 {
                    v___x_5255_ = lean_array_uget_borrowed(v_as_5249_, v_i_5250_);
                    crate::leanh::lean_inc(v___x_5255_);
                    crate::leanh::lean_inc(v___x_5248_);
                    crate::leanh::lean_inc_ref(v_f_5247_);
                    v___x_5256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5247_, v___x_5248_, v___x_5255_, v_b_5252_);
                    if crate::leanh::lean_obj_tag(v___x_5256_) == 0 {
                        v_a_5257_ = crate::leanh::lean_ctor_get(v___x_5256_, 0);
                        crate::leanh::lean_inc(v_a_5257_);
                        crate::leanh::lean_dec_ref_known(v___x_5256_, 1);
                        v___x_5258_ = 1usize;
                        v___x_5259_ = lean_usize_add(v_i_5250_, v___x_5258_);
                        v_i_5250_ = v___x_5259_;
                        v_b_5252_ = v_a_5257_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5248_);
                        crate::leanh::lean_dec_ref(v_f_5247_);
                        return v___x_5256_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5248_);
                    crate::leanh::lean_dec_ref(v_f_5247_);
                    v___x_5261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5261_, 0, v_b_5252_);
                    return v___x_5261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_f_5262_: *mut crate::leanh::LeanObject,
    mut v___x_5263_: *mut crate::leanh::LeanObject,
    mut v_x_5264_: *mut crate::leanh::LeanObject,
    mut v_x_5265_: usize,
    mut v_x_5266_: usize,
    mut v_x_5267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: usize = 0;
    let mut v_j_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: usize = 0;
    let mut v___x_5275_: usize = 0;
    let mut v___x_5276_: usize = 0;
    let mut v___x_5277_: usize = 0;
    let mut v___x_5278_: usize = 0;
    let mut v___x_5279_: usize = 0;
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: usize = 0;
    let mut v___x_5288_: usize = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: usize = 0;
    let mut v___x_5291_: usize = 0;
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: u8 = 0;
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: usize = 0;
    let mut v___x_5308_: usize = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5264_) == 0 {
                    v_cs_5269_ = crate::leanh::lean_ctor_get(v_x_5264_, 0);
                    crate::leanh::lean_inc_ref(v_cs_5269_);
                    crate::leanh::lean_dec_ref_known(v_x_5264_, 1);
                    v___x_5270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
                    v___x_5271_ = lean_usize_shift_right(v_x_5265_, v_x_5266_);
                    v_j_5272_ = lean_usize_to_nat(v___x_5271_);
                    v___x_5273_ = lean_array_get_borrowed(v___x_5270_, v_cs_5269_, v_j_5272_);
                    v___x_5274_ = 1usize;
                    v___x_5275_ = lean_usize_shift_left(v___x_5274_, v_x_5266_);
                    v___x_5276_ = lean_usize_sub(v___x_5275_, v___x_5274_);
                    v___x_5277_ = lean_usize_land(v_x_5265_, v___x_5276_);
                    v___x_5278_ = 5usize;
                    v___x_5279_ = lean_usize_sub(v_x_5266_, v___x_5278_);
                    crate::leanh::lean_inc(v___x_5273_);
                    crate::leanh::lean_inc(v___x_5263_);
                    crate::leanh::lean_inc_ref(v_f_5262_);
                    v___x_5280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5262_, v___x_5263_, v___x_5273_, v___x_5277_, v___x_5279_, v_x_5267_);
                    if crate::leanh::lean_obj_tag(v___x_5280_) == 0 {
                        v_a_5281_ = crate::leanh::lean_ctor_get(v___x_5280_, 0);
                        crate::leanh::lean_inc(v_a_5281_);
                        v___x_5282_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5283_ = lean_nat_add(v_j_5272_, v___x_5282_);
                        crate::leanh::lean_dec(v_j_5272_);
                        v___x_5284_ = lean_array_get_size(v_cs_5269_);
                        v___x_5285_ = lean_nat_dec_lt(v___x_5283_, v___x_5284_);
                        if v___x_5285_ == 0 {
                            crate::leanh::lean_dec(v___x_5283_);
                            crate::leanh::lean_dec(v_a_5281_);
                            crate::leanh::lean_dec_ref(v_cs_5269_);
                            crate::leanh::lean_dec(v___x_5263_);
                            crate::leanh::lean_dec_ref(v_f_5262_);
                            return v___x_5280_;
                        } else {
                            v___x_5286_ = lean_nat_dec_le(v___x_5284_, v___x_5284_);
                            if v___x_5286_ == 0 {
                                if v___x_5285_ == 0 {
                                    crate::leanh::lean_dec(v___x_5283_);
                                    crate::leanh::lean_dec(v_a_5281_);
                                    crate::leanh::lean_dec_ref(v_cs_5269_);
                                    crate::leanh::lean_dec(v___x_5263_);
                                    crate::leanh::lean_dec_ref(v_f_5262_);
                                    return v___x_5280_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_5280_, 1);
                                    v___x_5287_ = lean_usize_of_nat(v___x_5283_);
                                    crate::leanh::lean_dec(v___x_5283_);
                                    v___x_5288_ = lean_usize_of_nat(v___x_5284_);
                                    v___x_5289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5262_, v___x_5263_, v_cs_5269_, v___x_5287_, v___x_5288_, v_a_5281_);
                                    crate::leanh::lean_dec_ref(v_cs_5269_);
                                    return v___x_5289_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_5280_, 1);
                                v___x_5290_ = lean_usize_of_nat(v___x_5283_);
                                crate::leanh::lean_dec(v___x_5283_);
                                v___x_5291_ = lean_usize_of_nat(v___x_5284_);
                                v___x_5292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5262_, v___x_5263_, v_cs_5269_, v___x_5290_, v___x_5291_, v_a_5281_);
                                crate::leanh::lean_dec_ref(v_cs_5269_);
                                return v___x_5292_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_5272_);
                        crate::leanh::lean_dec_ref(v_cs_5269_);
                        crate::leanh::lean_dec(v___x_5263_);
                        crate::leanh::lean_dec_ref(v_f_5262_);
                        return v___x_5280_;
                    }
                } else {
                    v_vs_5293_ = crate::leanh::lean_ctor_get(v_x_5264_, 0);
                    v_isSharedCheck_5313_ = (!crate::leanh::lean_is_exclusive(v_x_5264_)) as u8;
                    if v_isSharedCheck_5313_ == 0 {
                        v___x_5295_ = v_x_5264_;
                        v_isShared_5296_ = v_isSharedCheck_5313_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5293_);
                        crate::leanh::lean_dec(v_x_5264_);
                        v___x_5295_ = crate::leanh::lean_box(0);
                        v_isShared_5296_ = v_isSharedCheck_5313_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5297_ = lean_usize_to_nat(v_x_5265_);
                v___x_5298_ = lean_array_get_size(v_vs_5293_);
                v___x_5299_ = lean_nat_dec_lt(v___x_5297_, v___x_5298_);
                if v___x_5299_ == 0 {
                    crate::leanh::lean_dec(v___x_5297_);
                    crate::leanh::lean_dec_ref(v_vs_5293_);
                    crate::leanh::lean_dec(v___x_5263_);
                    crate::leanh::lean_dec_ref(v_f_5262_);
                    if v_isShared_5296_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5295_, 0);
                        crate::leanh::lean_ctor_set(v___x_5295_, 0, v_x_5267_);
                        v___x_5301_ = v___x_5295_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_x_5267_);
                        v___x_5301_ = v_reuseFailAlloc_5302_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5303_ = lean_nat_dec_le(v___x_5298_, v___x_5298_);
                    if v___x_5303_ == 0 {
                        if v___x_5299_ == 0 {
                            crate::leanh::lean_dec(v___x_5297_);
                            crate::leanh::lean_dec_ref(v_vs_5293_);
                            crate::leanh::lean_dec(v___x_5263_);
                            crate::leanh::lean_dec_ref(v_f_5262_);
                            if v_isShared_5296_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_5295_, 0);
                                crate::leanh::lean_ctor_set(v___x_5295_, 0, v_x_5267_);
                                v___x_5305_ = v___x_5295_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5306_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_x_5267_);
                                v___x_5305_ = v_reuseFailAlloc_5306_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5295_);
                            v___x_5307_ = lean_usize_of_nat(v___x_5297_);
                            crate::leanh::lean_dec(v___x_5297_);
                            v___x_5308_ = lean_usize_of_nat(v___x_5298_);
                            v___x_5309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5262_, v___x_5263_, v_vs_5293_, v___x_5307_, v___x_5308_, v_x_5267_);
                            crate::leanh::lean_dec_ref(v_vs_5293_);
                            return v___x_5309_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5295_);
                        v___x_5310_ = lean_usize_of_nat(v___x_5297_);
                        crate::leanh::lean_dec(v___x_5297_);
                        v___x_5311_ = lean_usize_of_nat(v___x_5298_);
                        v___x_5312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5262_, v___x_5263_, v_vs_5293_, v___x_5310_, v___x_5311_, v_x_5267_);
                        crate::leanh::lean_dec_ref(v_vs_5293_);
                        return v___x_5312_;
                    }
                }
            }
            2 => {
                return v___x_5301_;
            }
            3 => {
                return v___x_5305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_5314_: *mut crate::leanh::LeanObject,
    mut v___x_5315_: *mut crate::leanh::LeanObject,
    mut v_t_5316_: *mut crate::leanh::LeanObject,
    mut v_init_5317_: *mut crate::leanh::LeanObject,
    mut v_start_5318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: u8 = 0;
    v___x_5320_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5321_ = lean_nat_dec_eq(v_start_5318_, v___x_5320_);
    if v___x_5321_ == 0 {
        let mut v_root_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_5324_: usize = 0;
        let mut v_tailOff_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5326_: u8 = 0;
        v_root_5322_ = crate::leanh::lean_ctor_get(v_t_5316_, 0);
        crate::leanh::lean_inc_ref(v_root_5322_);
        v_tail_5323_ = crate::leanh::lean_ctor_get(v_t_5316_, 1);
        crate::leanh::lean_inc_ref(v_tail_5323_);
        v_shift_5324_ = crate::leanh::lean_ctor_get_usize(v_t_5316_, 4);
        v_tailOff_5325_ = crate::leanh::lean_ctor_get(v_t_5316_, 3);
        crate::leanh::lean_inc(v_tailOff_5325_);
        crate::leanh::lean_dec_ref(v_t_5316_);
        v___x_5326_ = lean_nat_dec_le(v_tailOff_5325_, v_start_5318_);
        if v___x_5326_ == 0 {
            let mut v___x_5327_: usize = 0;
            let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_tailOff_5325_);
            v___x_5327_ = lean_usize_of_nat(v_start_5318_);
            crate::leanh::lean_inc(v___x_5315_);
            crate::leanh::lean_inc_ref(v_f_5314_);
            v___x_5328_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5314_, v___x_5315_, v_root_5322_, v___x_5327_, v_shift_5324_, v_init_5317_);
            if crate::leanh::lean_obj_tag(v___x_5328_) == 0 {
                let mut v_a_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5331_: u8 = 0;
                v_a_5329_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
                crate::leanh::lean_inc(v_a_5329_);
                v___x_5330_ = lean_array_get_size(v_tail_5323_);
                v___x_5331_ = lean_nat_dec_lt(v___x_5320_, v___x_5330_);
                if v___x_5331_ == 0 {
                    crate::leanh::lean_dec(v_a_5329_);
                    crate::leanh::lean_dec_ref(v_tail_5323_);
                    crate::leanh::lean_dec(v___x_5315_);
                    crate::leanh::lean_dec_ref(v_f_5314_);
                    return v___x_5328_;
                } else {
                    let mut v___x_5332_: u8 = 0;
                    v___x_5332_ = lean_nat_dec_le(v___x_5330_, v___x_5330_);
                    if v___x_5332_ == 0 {
                        if v___x_5331_ == 0 {
                            crate::leanh::lean_dec(v_a_5329_);
                            crate::leanh::lean_dec_ref(v_tail_5323_);
                            crate::leanh::lean_dec(v___x_5315_);
                            crate::leanh::lean_dec_ref(v_f_5314_);
                            return v___x_5328_;
                        } else {
                            let mut v___x_5333_: usize = 0;
                            let mut v___x_5334_: usize = 0;
                            let mut v___x_5335_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_5328_, 1);
                            v___x_5333_ = 0usize;
                            v___x_5334_ = lean_usize_of_nat(v___x_5330_);
                            v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5333_, v___x_5334_, v_a_5329_);
                            crate::leanh::lean_dec_ref(v_tail_5323_);
                            return v___x_5335_;
                        }
                    } else {
                        let mut v___x_5336_: usize = 0;
                        let mut v___x_5337_: usize = 0;
                        let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_5328_, 1);
                        v___x_5336_ = 0usize;
                        v___x_5337_ = lean_usize_of_nat(v___x_5330_);
                        v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5336_, v___x_5337_, v_a_5329_);
                        crate::leanh::lean_dec_ref(v_tail_5323_);
                        return v___x_5338_;
                    }
                }
            } else {
                crate::leanh::lean_dec_ref(v_tail_5323_);
                crate::leanh::lean_dec(v___x_5315_);
                crate::leanh::lean_dec_ref(v_f_5314_);
                return v___x_5328_;
            }
        } else {
            let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5341_: u8 = 0;
            crate::leanh::lean_dec_ref(v_root_5322_);
            v___x_5339_ = lean_nat_sub(v_start_5318_, v_tailOff_5325_);
            crate::leanh::lean_dec(v_tailOff_5325_);
            v___x_5340_ = lean_array_get_size(v_tail_5323_);
            v___x_5341_ = lean_nat_dec_lt(v___x_5339_, v___x_5340_);
            if v___x_5341_ == 0 {
                let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_5339_);
                crate::leanh::lean_dec_ref(v_tail_5323_);
                crate::leanh::lean_dec(v___x_5315_);
                crate::leanh::lean_dec_ref(v_f_5314_);
                v___x_5342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5342_, 0, v_init_5317_);
                return v___x_5342_;
            } else {
                let mut v___x_5343_: u8 = 0;
                v___x_5343_ = lean_nat_dec_le(v___x_5340_, v___x_5340_);
                if v___x_5343_ == 0 {
                    if v___x_5341_ == 0 {
                        let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_5339_);
                        crate::leanh::lean_dec_ref(v_tail_5323_);
                        crate::leanh::lean_dec(v___x_5315_);
                        crate::leanh::lean_dec_ref(v_f_5314_);
                        v___x_5344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5344_, 0, v_init_5317_);
                        return v___x_5344_;
                    } else {
                        let mut v___x_5345_: usize = 0;
                        let mut v___x_5346_: usize = 0;
                        let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5345_ = lean_usize_of_nat(v___x_5339_);
                        crate::leanh::lean_dec(v___x_5339_);
                        v___x_5346_ = lean_usize_of_nat(v___x_5340_);
                        v___x_5347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5345_, v___x_5346_, v_init_5317_);
                        crate::leanh::lean_dec_ref(v_tail_5323_);
                        return v___x_5347_;
                    }
                } else {
                    let mut v___x_5348_: usize = 0;
                    let mut v___x_5349_: usize = 0;
                    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5348_ = lean_usize_of_nat(v___x_5339_);
                    crate::leanh::lean_dec(v___x_5339_);
                    v___x_5349_ = lean_usize_of_nat(v___x_5340_);
                    v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5348_, v___x_5349_, v_init_5317_);
                    crate::leanh::lean_dec_ref(v_tail_5323_);
                    return v___x_5350_;
                }
            }
        }
    } else {
        let mut v_root_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_root_5351_ = crate::leanh::lean_ctor_get(v_t_5316_, 0);
        crate::leanh::lean_inc_ref(v_root_5351_);
        v_tail_5352_ = crate::leanh::lean_ctor_get(v_t_5316_, 1);
        crate::leanh::lean_inc_ref(v_tail_5352_);
        crate::leanh::lean_dec_ref(v_t_5316_);
        crate::leanh::lean_inc(v___x_5315_);
        crate::leanh::lean_inc_ref(v_f_5314_);
        v___x_5353_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5314_, v___x_5315_, v_root_5351_, v_init_5317_);
        if crate::leanh::lean_obj_tag(v___x_5353_) == 0 {
            let mut v_a_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5356_: u8 = 0;
            v_a_5354_ = crate::leanh::lean_ctor_get(v___x_5353_, 0);
            crate::leanh::lean_inc(v_a_5354_);
            v___x_5355_ = lean_array_get_size(v_tail_5352_);
            v___x_5356_ = lean_nat_dec_lt(v___x_5320_, v___x_5355_);
            if v___x_5356_ == 0 {
                crate::leanh::lean_dec(v_a_5354_);
                crate::leanh::lean_dec_ref(v_tail_5352_);
                crate::leanh::lean_dec(v___x_5315_);
                crate::leanh::lean_dec_ref(v_f_5314_);
                return v___x_5353_;
            } else {
                let mut v___x_5357_: u8 = 0;
                v___x_5357_ = lean_nat_dec_le(v___x_5355_, v___x_5355_);
                if v___x_5357_ == 0 {
                    if v___x_5356_ == 0 {
                        crate::leanh::lean_dec(v_a_5354_);
                        crate::leanh::lean_dec_ref(v_tail_5352_);
                        crate::leanh::lean_dec(v___x_5315_);
                        crate::leanh::lean_dec_ref(v_f_5314_);
                        return v___x_5353_;
                    } else {
                        let mut v___x_5358_: usize = 0;
                        let mut v___x_5359_: usize = 0;
                        let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_5353_, 1);
                        v___x_5358_ = 0usize;
                        v___x_5359_ = lean_usize_of_nat(v___x_5355_);
                        v___x_5360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5352_, v___x_5358_, v___x_5359_, v_a_5354_);
                        crate::leanh::lean_dec_ref(v_tail_5352_);
                        return v___x_5360_;
                    }
                } else {
                    let mut v___x_5361_: usize = 0;
                    let mut v___x_5362_: usize = 0;
                    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_5353_, 1);
                    v___x_5361_ = 0usize;
                    v___x_5362_ = lean_usize_of_nat(v___x_5355_);
                    v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5352_, v___x_5361_, v___x_5362_, v_a_5354_);
                    crate::leanh::lean_dec_ref(v_tail_5352_);
                    return v___x_5363_;
                }
            }
        } else {
            crate::leanh::lean_dec_ref(v_tail_5352_);
            crate::leanh::lean_dec(v___x_5315_);
            crate::leanh::lean_dec_ref(v_f_5314_);
            return v___x_5353_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(
    mut v_f_5364_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_x_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut v_unused_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_5367_) {
                0 => {
                    v_i_5369_ = crate::leanh::lean_ctor_get(v_x_5367_, 0);
                    crate::leanh::lean_inc_ref(v_i_5369_);
                    v_t_5370_ = crate::leanh::lean_ctor_get(v_x_5367_, 1);
                    crate::leanh::lean_inc_ref(v_t_5370_);
                    crate::leanh::lean_dec_ref_known(v_x_5367_, 2);
                    v___x_5371_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_5369_,
                        v_ctx_x3f_5365_,
                    );
                    v_ctx_x3f_5365_ = v___x_5371_;
                    v_x_5367_ = v_t_5370_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_5373_ = crate::leanh::lean_ctor_get(v_x_5367_, 0);
                    crate::leanh::lean_inc_ref(v_i_5373_);
                    v_children_5374_ = crate::leanh::lean_ctor_get(v_x_5367_, 1);
                    crate::leanh::lean_inc_ref(v_children_5374_);
                    crate::leanh::lean_dec_ref_known(v_x_5367_, 2);
                    if crate::leanh::lean_obj_tag(v_ctx_x3f_5365_) == 0 {
                        v_a_5376_ = v_a_5366_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5380_ = crate::leanh::lean_ctor_get(v_ctx_x3f_5365_, 0);
                        crate::leanh::lean_inc_ref(v_f_5364_);
                        crate::leanh::lean_inc_ref(v_i_5373_);
                        crate::leanh::lean_inc(v_val_5380_);
                        v___x_5381_ = crate::leanh::lean_apply_4(
                            v_f_5364_,
                            v_val_5380_,
                            v_i_5373_,
                            v_a_5366_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5381_) == 0 {
                            v_a_5382_ = crate::leanh::lean_ctor_get(v___x_5381_, 0);
                            crate::leanh::lean_inc(v_a_5382_);
                            crate::leanh::lean_dec_ref_known(v___x_5381_, 1);
                            v_a_5376_ = v_a_5382_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_ctx_x3f_5365_, 1);
                            crate::leanh::lean_dec_ref(v_children_5374_);
                            crate::leanh::lean_dec_ref(v_i_5373_);
                            crate::leanh::lean_dec_ref(v_f_5364_);
                            return v___x_5381_;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_ctx_x3f_5365_);
                    crate::leanh::lean_dec_ref(v_f_5364_);
                    v_isSharedCheck_5389_ = (!crate::leanh::lean_is_exclusive(v_x_5367_)) as u8;
                    if v_isSharedCheck_5389_ == 0 {
                        v_unused_5390_ = crate::leanh::lean_ctor_get(v_x_5367_, 0);
                        crate::leanh::lean_dec(v_unused_5390_);
                        v___x_5384_ = v_x_5367_;
                        v_isShared_5385_ = v_isSharedCheck_5389_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_5367_);
                        v___x_5384_ = crate::leanh::lean_box(0);
                        v_isShared_5385_ = v_isSharedCheck_5389_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5377_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_5365_, v_i_5373_);
                crate::leanh::lean_dec_ref(v_i_5373_);
                v___x_5378_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5379_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5364_, v___x_5377_, v_children_5374_, v_a_5376_, v___x_5378_);
                return v___x_5379_;
            }
            2 => {
                if v_isShared_5385_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5384_, 0);
                    crate::leanh::lean_ctor_set(v___x_5384_, 0, v_a_5366_);
                    v___x_5387_ = v___x_5384_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5366_);
                    v___x_5387_ = v_reuseFailAlloc_5388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_f_5391_: *mut crate::leanh::LeanObject,
    mut v___x_5392_: *mut crate::leanh::LeanObject,
    mut v_as_5393_: *mut crate::leanh::LeanObject,
    mut v_i_5394_: usize,
    mut v_stop_5395_: usize,
    mut v_b_5396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5398_: u8 = 0;
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: usize = 0;
    let mut v___x_5403_: usize = 0;
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5398_ = lean_usize_dec_eq(v_i_5394_, v_stop_5395_);
                if v___x_5398_ == 0 {
                    v___x_5399_ = lean_array_uget_borrowed(v_as_5393_, v_i_5394_);
                    crate::leanh::lean_inc(v___x_5399_);
                    crate::leanh::lean_inc(v___x_5392_);
                    crate::leanh::lean_inc_ref(v_f_5391_);
                    v___x_5400_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5391_, v___x_5392_, v_b_5396_, v___x_5399_);
                    if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                        v_a_5401_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                        crate::leanh::lean_inc(v_a_5401_);
                        crate::leanh::lean_dec_ref_known(v___x_5400_, 1);
                        v___x_5402_ = 1usize;
                        v___x_5403_ = lean_usize_add(v_i_5394_, v___x_5402_);
                        v_i_5394_ = v___x_5403_;
                        v_b_5396_ = v_a_5401_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5392_);
                        crate::leanh::lean_dec_ref(v_f_5391_);
                        return v___x_5400_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5392_);
                    crate::leanh::lean_dec_ref(v_f_5391_);
                    v___x_5405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5405_, 0, v_b_5396_);
                    return v___x_5405_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_f_5406_: *mut crate::leanh::LeanObject,
    mut v___x_5407_: *mut crate::leanh::LeanObject,
    mut v_as_5408_: *mut crate::leanh::LeanObject,
    mut v_i_5409_: *mut crate::leanh::LeanObject,
    mut v_stop_5410_: *mut crate::leanh::LeanObject,
    mut v_b_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5413_: usize = 0;
    let mut v_stop_boxed_5414_: usize = 0;
    let mut v_res_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5413_ = crate::leanh::lean_unbox_usize(v_i_5409_);
    crate::leanh::lean_dec(v_i_5409_);
    v_stop_boxed_5414_ = crate::leanh::lean_unbox_usize(v_stop_5410_);
    crate::leanh::lean_dec(v_stop_5410_);
    v_res_5415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5406_, v___x_5407_, v_as_5408_, v_i_boxed_5413_, v_stop_boxed_5414_, v_b_5411_);
    crate::leanh::lean_dec_ref(v_as_5408_);
    return v_res_5415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_f_5416_: *mut crate::leanh::LeanObject,
    mut v___x_5417_: *mut crate::leanh::LeanObject,
    mut v_as_5418_: *mut crate::leanh::LeanObject,
    mut v_i_5419_: *mut crate::leanh::LeanObject,
    mut v_stop_5420_: *mut crate::leanh::LeanObject,
    mut v_b_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5423_: usize = 0;
    let mut v_stop_boxed_5424_: usize = 0;
    let mut v_res_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5423_ = crate::leanh::lean_unbox_usize(v_i_5419_);
    crate::leanh::lean_dec(v_i_5419_);
    v_stop_boxed_5424_ = crate::leanh::lean_unbox_usize(v_stop_5420_);
    crate::leanh::lean_dec(v_stop_5420_);
    v_res_5425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5416_, v___x_5417_, v_as_5418_, v_i_boxed_5423_, v_stop_boxed_5424_, v_b_5421_);
    crate::leanh::lean_dec_ref(v_as_5418_);
    return v_res_5425_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_5426_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_5427_: *mut crate::leanh::LeanObject,
    mut v_a_5428_: *mut crate::leanh::LeanObject,
    mut v_x_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5431_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5426_, v_ctx_x3f_5427_, v_a_5428_, v_x_5429_);
    return v_res_5431_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_f_5432_: *mut crate::leanh::LeanObject,
    mut v___x_5433_: *mut crate::leanh::LeanObject,
    mut v_x_5434_: *mut crate::leanh::LeanObject,
    mut v_x_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5437_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5432_, v___x_5433_, v_x_5434_, v_x_5435_);
    return v_res_5437_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_f_5438_: *mut crate::leanh::LeanObject,
    mut v___x_5439_: *mut crate::leanh::LeanObject,
    mut v_x_5440_: *mut crate::leanh::LeanObject,
    mut v_x_5441_: *mut crate::leanh::LeanObject,
    mut v_x_5442_: *mut crate::leanh::LeanObject,
    mut v_x_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2919__boxed_5445_: usize = 0;
    let mut v_x_2920__boxed_5446_: usize = 0;
    let mut v_res_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2919__boxed_5445_ = crate::leanh::lean_unbox_usize(v_x_5441_);
    crate::leanh::lean_dec(v_x_5441_);
    v_x_2920__boxed_5446_ = crate::leanh::lean_unbox_usize(v_x_5442_);
    crate::leanh::lean_dec(v_x_5442_);
    v_res_5447_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5438_, v___x_5439_, v_x_5440_, v_x_2919__boxed_5445_, v_x_2920__boxed_5446_, v_x_5443_);
    return v_res_5447_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_f_5448_: *mut crate::leanh::LeanObject,
    mut v___x_5449_: *mut crate::leanh::LeanObject,
    mut v_t_5450_: *mut crate::leanh::LeanObject,
    mut v_init_5451_: *mut crate::leanh::LeanObject,
    mut v_start_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5448_, v___x_5449_, v_t_5450_, v_init_5451_, v_start_5452_);
    crate::leanh::lean_dec(v_start_5452_);
    return v_res_5454_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(
    mut v_f_5455_: *mut crate::leanh::LeanObject,
    mut v_init_5456_: *mut crate::leanh::LeanObject,
    mut v_x_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5459_ = crate::leanh::lean_box(0);
    v___x_5460_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5455_, v___x_5459_, v_init_5456_, v_x_5457_);
    return v___x_5460_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(
    mut v_f_5461_: *mut crate::leanh::LeanObject,
    mut v_init_5462_: *mut crate::leanh::LeanObject,
    mut v_x_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5465_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_5461_, v_init_5462_, v_x_5463_);
    return v_res_5465_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(
    mut v_f_5466_: *mut crate::leanh::LeanObject,
    mut v_ctx_5467_: *mut crate::leanh::LeanObject,
    mut v_info_5468_: *mut crate::leanh::LeanObject,
    mut v_result_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5485_: u8 = 0;
    let mut v_a_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_5468_) == 1 {
                    v_i_5471_ = crate::leanh::lean_ctor_get(v_info_5468_, 0);
                    crate::leanh::lean_inc_ref(v_i_5471_);
                    crate::leanh::lean_dec_ref_known(v_info_5468_, 1);
                    v___x_5472_ = crate::leanh::lean_apply_3(
                        v_f_5466_,
                        v_ctx_5467_,
                        v_i_5471_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5472_) == 0 {
                        v_a_5473_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5485_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5485_ == 0 {
                            v___x_5475_ = v___x_5472_;
                            v_isShared_5476_ = v_isSharedCheck_5485_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5473_);
                            crate::leanh::lean_dec(v___x_5472_);
                            v___x_5475_ = crate::leanh::lean_box(0);
                            v_isShared_5476_ = v_isSharedCheck_5485_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_result_5469_);
                        v_a_5486_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5493_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5493_ == 0 {
                            v___x_5488_ = v___x_5472_;
                            v_isShared_5489_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5486_);
                            crate::leanh::lean_dec(v___x_5472_);
                            v___x_5488_ = crate::leanh::lean_box(0);
                            v_isShared_5489_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_5468_);
                    crate::leanh::lean_dec_ref(v_ctx_5467_);
                    crate::leanh::lean_dec_ref(v_f_5466_);
                    v___x_5494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5494_, 0, v_result_5469_);
                    return v___x_5494_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5473_) == 0 {
                    if v_isShared_5476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5475_, 0, v_result_5469_);
                        v___x_5478_ = v___x_5475_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_result_5469_);
                        v___x_5478_ = v_reuseFailAlloc_5479_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5480_ = crate::leanh::lean_ctor_get(v_a_5473_, 0);
                    crate::leanh::lean_inc(v_val_5480_);
                    crate::leanh::lean_dec_ref_known(v_a_5473_, 1);
                    v___x_5481_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5481_, 0, v_val_5480_);
                    crate::leanh::lean_ctor_set(v___x_5481_, 1, v_result_5469_);
                    if v_isShared_5476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5475_, 0, v___x_5481_);
                        v___x_5483_ = v___x_5475_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
                        v___x_5483_ = v_reuseFailAlloc_5484_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5478_;
            }
            3 => {
                return v___x_5483_;
            }
            4 => {
                if v_isShared_5489_ == 0 {
                    v___x_5491_ = v___x_5488_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
                    v___x_5491_ = v_reuseFailAlloc_5492_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed(
    mut v_f_5495_: *mut crate::leanh::LeanObject,
    mut v_ctx_5496_: *mut crate::leanh::LeanObject,
    mut v_info_5497_: *mut crate::leanh::LeanObject,
    mut v_result_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_5495_, v_ctx_5496_, v_info_5497_, v_result_5498_);
    return v_res_5500_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
    mut v_t_5501_: *mut crate::leanh::LeanObject,
    mut v_f_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5504_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
    crate::leanh::lean_closure_set(v___f_5504_, 0, v_f_5502_);
    v___x_5505_ = crate::leanh::lean_box(0);
    v___x_5506_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_5504_, v___x_5505_, v_t_5501_);
    return v___x_5506_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(
    mut v_t_5507_: *mut crate::leanh::LeanObject,
    mut v_f_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5507_, v_f_5508_,
        );
    return v_res_5510_;
}
pub unsafe fn l_Lean_Linter_List_binders(
    mut v_t_5511_: *mut crate::leanh::LeanObject,
    mut v_p_5512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5514_ = crate::leanh::lean_alloc_closure(
        l_Lean_Linter_List_binders___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5514_, 0, v_p_5512_);
    v___x_5515_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5511_,
            v___f_5514_,
        );
    return v___x_5515_;
}
pub unsafe fn l_Lean_Linter_List_binders___boxed(
    mut v_t_5516_: *mut crate::leanh::LeanObject,
    mut v_p_5517_: *mut crate::leanh::LeanObject,
    mut v_a_5518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5519_ = l_Lean_Linter_List_binders(v_t_5516_, v_p_5517_);
    return v_res_5519_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(
    mut v_00_u03b1_5520_: *mut crate::leanh::LeanObject,
    mut v_t_5521_: *mut crate::leanh::LeanObject,
    mut v_f_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5524_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5521_, v_f_5522_,
        );
    return v___x_5524_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(
    mut v_00_u03b1_5525_: *mut crate::leanh::LeanObject,
    mut v_t_5526_: *mut crate::leanh::LeanObject,
    mut v_f_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5529_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(
        v_00_u03b1_5525_,
        v_t_5526_,
        v_f_5527_,
    );
    return v_res_5529_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(
    mut v_00_u03b1_5530_: *mut crate::leanh::LeanObject,
    mut v_f_5531_: *mut crate::leanh::LeanObject,
    mut v_init_5532_: *mut crate::leanh::LeanObject,
    mut v_x_5533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5535_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_5531_, v_init_5532_, v_x_5533_);
    return v___x_5535_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(
    mut v_00_u03b1_5536_: *mut crate::leanh::LeanObject,
    mut v_f_5537_: *mut crate::leanh::LeanObject,
    mut v_init_5538_: *mut crate::leanh::LeanObject,
    mut v_x_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5541_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_5536_, v_f_5537_, v_init_5538_, v_x_5539_);
    return v_res_5541_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(
    mut v_00_u03b1_5542_: *mut crate::leanh::LeanObject,
    mut v_f_5543_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_5544_: *mut crate::leanh::LeanObject,
    mut v_a_5545_: *mut crate::leanh::LeanObject,
    mut v_x_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5548_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5543_, v_ctx_x3f_5544_, v_a_5545_, v_x_5546_);
    return v___x_5548_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_5549_: *mut crate::leanh::LeanObject,
    mut v_f_5550_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_5551_: *mut crate::leanh::LeanObject,
    mut v_a_5552_: *mut crate::leanh::LeanObject,
    mut v_x_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5555_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_5549_, v_f_5550_, v_ctx_x3f_5551_, v_a_5552_, v_x_5553_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_5556_: *mut crate::leanh::LeanObject,
    mut v_f_5557_: *mut crate::leanh::LeanObject,
    mut v___x_5558_: *mut crate::leanh::LeanObject,
    mut v_t_5559_: *mut crate::leanh::LeanObject,
    mut v_init_5560_: *mut crate::leanh::LeanObject,
    mut v_start_5561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5557_, v___x_5558_, v_t_5559_, v_init_5560_, v_start_5561_);
    return v___x_5563_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_5564_: *mut crate::leanh::LeanObject,
    mut v_f_5565_: *mut crate::leanh::LeanObject,
    mut v___x_5566_: *mut crate::leanh::LeanObject,
    mut v_t_5567_: *mut crate::leanh::LeanObject,
    mut v_init_5568_: *mut crate::leanh::LeanObject,
    mut v_start_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5571_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_5564_, v_f_5565_, v___x_5566_, v_t_5567_, v_init_5568_, v_start_5569_);
    crate::leanh::lean_dec(v_start_5569_);
    return v_res_5571_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b1_5572_: *mut crate::leanh::LeanObject,
    mut v_f_5573_: *mut crate::leanh::LeanObject,
    mut v___x_5574_: *mut crate::leanh::LeanObject,
    mut v_x_5575_: *mut crate::leanh::LeanObject,
    mut v_x_5576_: usize,
    mut v_x_5577_: usize,
    mut v_x_5578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5580_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5573_, v___x_5574_, v_x_5575_, v_x_5576_, v_x_5577_, v_x_5578_);
    return v___x_5580_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_5581_: *mut crate::leanh::LeanObject,
    mut v_f_5582_: *mut crate::leanh::LeanObject,
    mut v___x_5583_: *mut crate::leanh::LeanObject,
    mut v_x_5584_: *mut crate::leanh::LeanObject,
    mut v_x_5585_: *mut crate::leanh::LeanObject,
    mut v_x_5586_: *mut crate::leanh::LeanObject,
    mut v_x_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3339__boxed_5589_: usize = 0;
    let mut v_x_3340__boxed_5590_: usize = 0;
    let mut v_res_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3339__boxed_5589_ = crate::leanh::lean_unbox_usize(v_x_5585_);
    crate::leanh::lean_dec(v_x_5585_);
    v_x_3340__boxed_5590_ = crate::leanh::lean_unbox_usize(v_x_5586_);
    crate::leanh::lean_dec(v_x_5586_);
    v_res_5591_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_5581_, v_f_5582_, v___x_5583_, v_x_5584_, v_x_3339__boxed_5589_, v_x_3340__boxed_5590_, v_x_5587_);
    return v_res_5591_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_5592_: *mut crate::leanh::LeanObject,
    mut v_f_5593_: *mut crate::leanh::LeanObject,
    mut v___x_5594_: *mut crate::leanh::LeanObject,
    mut v_as_5595_: *mut crate::leanh::LeanObject,
    mut v_i_5596_: usize,
    mut v_stop_5597_: usize,
    mut v_b_5598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5593_, v___x_5594_, v_as_5595_, v_i_5596_, v_stop_5597_, v_b_5598_);
    return v___x_5600_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_5601_: *mut crate::leanh::LeanObject,
    mut v_f_5602_: *mut crate::leanh::LeanObject,
    mut v___x_5603_: *mut crate::leanh::LeanObject,
    mut v_as_5604_: *mut crate::leanh::LeanObject,
    mut v_i_5605_: *mut crate::leanh::LeanObject,
    mut v_stop_5606_: *mut crate::leanh::LeanObject,
    mut v_b_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5609_: usize = 0;
    let mut v_stop_boxed_5610_: usize = 0;
    let mut v_res_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5609_ = crate::leanh::lean_unbox_usize(v_i_5605_);
    crate::leanh::lean_dec(v_i_5605_);
    v_stop_boxed_5610_ = crate::leanh::lean_unbox_usize(v_stop_5606_);
    crate::leanh::lean_dec(v_stop_5606_);
    v_res_5611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_5601_, v_f_5602_, v___x_5603_, v_as_5604_, v_i_boxed_5609_, v_stop_boxed_5610_, v_b_5607_);
    crate::leanh::lean_dec_ref(v_as_5604_);
    return v_res_5611_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(
    mut v_00_u03b1_5612_: *mut crate::leanh::LeanObject,
    mut v_f_5613_: *mut crate::leanh::LeanObject,
    mut v___x_5614_: *mut crate::leanh::LeanObject,
    mut v_x_5615_: *mut crate::leanh::LeanObject,
    mut v_x_5616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5618_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5613_, v___x_5614_, v_x_5615_, v_x_5616_);
    return v___x_5618_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_5619_: *mut crate::leanh::LeanObject,
    mut v_f_5620_: *mut crate::leanh::LeanObject,
    mut v___x_5621_: *mut crate::leanh::LeanObject,
    mut v_x_5622_: *mut crate::leanh::LeanObject,
    mut v_x_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_5619_, v_f_5620_, v___x_5621_, v_x_5622_, v_x_5623_);
    return v_res_5625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b1_5626_: *mut crate::leanh::LeanObject,
    mut v_f_5627_: *mut crate::leanh::LeanObject,
    mut v___x_5628_: *mut crate::leanh::LeanObject,
    mut v_as_5629_: *mut crate::leanh::LeanObject,
    mut v_i_5630_: usize,
    mut v_stop_5631_: usize,
    mut v_b_5632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5627_, v___x_5628_, v_as_5629_, v_i_5630_, v_stop_5631_, v_b_5632_);
    return v___x_5634_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_00_u03b1_5635_: *mut crate::leanh::LeanObject,
    mut v_f_5636_: *mut crate::leanh::LeanObject,
    mut v___x_5637_: *mut crate::leanh::LeanObject,
    mut v_as_5638_: *mut crate::leanh::LeanObject,
    mut v_i_5639_: *mut crate::leanh::LeanObject,
    mut v_stop_5640_: *mut crate::leanh::LeanObject,
    mut v_b_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5643_: usize = 0;
    let mut v_stop_boxed_5644_: usize = 0;
    let mut v_res_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5643_ = crate::leanh::lean_unbox_usize(v_i_5639_);
    crate::leanh::lean_dec(v_i_5639_);
    v_stop_boxed_5644_ = crate::leanh::lean_unbox_usize(v_stop_5640_);
    crate::leanh::lean_dec(v_stop_5640_);
    v_res_5645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_5635_, v_f_5636_, v___x_5637_, v_as_5638_, v_i_boxed_5643_, v_stop_boxed_5644_, v_b_5641_);
    crate::leanh::lean_dec_ref(v_as_5638_);
    return v_res_5645_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5647_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0;
    v___x_5648_ = l_Lean_stringToMessageData(v___x_5647_);
    return v___x_5648_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(
    mut v_as_x27_5652_: *mut crate::leanh::LeanObject,
    mut v_b_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: u8 = 0;
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: u8 = 0;
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5652_) == 0 {
                    v___x_5657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5657_, 0, v_b_5653_);
                    return v___x_5657_;
                } else {
                    v_head_5658_ = crate::leanh::lean_ctor_get(v_as_x27_5652_, 0);
                    v_snd_5659_ = crate::leanh::lean_ctor_get(v_head_5658_, 1);
                    v_tail_5660_ = crate::leanh::lean_ctor_get(v_as_x27_5652_, 1);
                    v_fst_5661_ = crate::leanh::lean_ctor_get(v_head_5658_, 0);
                    v_fst_5662_ = crate::leanh::lean_ctor_get(v_snd_5659_, 0);
                    v_snd_5663_ = crate::leanh::lean_ctor_get(v_snd_5659_, 1);
                    v___x_5664_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_fst_5662_) == 1 {
                        v_str_5665_ = crate::leanh::lean_ctor_get(v_fst_5662_, 1);
                        crate::leanh::lean_inc_ref(v_str_5665_);
                        v___x_5666_ = l_Lean_Linter_List_stripBinderName(v_str_5665_);
                        v___x_5667_ = l_Lean_Linter_List_allowedArrayNames;
                        v___x_5668_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5666_,
                            v___x_5667_,
                        );
                        if v___x_5668_ == 0 {
                            v___x_5669_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5680_ = l_Lean_Expr_getAppNumArgs(v_snd_5663_);
                            v___x_5681_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5682_ = lean_nat_sub(v___x_5680_, v___x_5681_);
                            crate::leanh::lean_dec(v___x_5680_);
                            v___x_5683_ = l_Lean_Expr_getRevArg_x21(v_snd_5663_, v___x_5682_);
                            v___x_5684_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                            v___x_5685_ = l_Lean_Expr_isAppOf(v___x_5683_, v___x_5684_);
                            if v___x_5685_ == 0 {
                                v___x_5686_ =
                                    l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                                v___x_5687_ = l_Lean_Expr_isAppOf(v___x_5683_, v___x_5686_);
                                crate::leanh::lean_dec_ref(v___x_5683_);
                                if v___x_5687_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5683_);
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5666_);
                            v_as_x27_5652_ = v_tail_5660_;
                            v_b_5653_ = v___x_5664_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_5652_ = v_tail_5660_;
                        v_b_5653_ = v___x_5664_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
                v___x_5672_ = l_Lean_stringToMessageData(v___x_5666_);
                v___x_5673_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5673_, 0, v___x_5671_);
                crate::leanh::lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                v___x_5674_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5669_,
                    v_fst_5661_,
                    v___x_5673_,
                    v___y_5654_,
                    v___y_5655_,
                );
                if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5674_, 1);
                    v_as_x27_5652_ = v_tail_5660_;
                    v_b_5653_ = v___x_5664_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5674_;
                }
            }
            2 => {
                v___x_5677_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2;
                v___x_5678_ = lean_string_dec_eq(v___x_5666_, v___x_5677_);
                if v___x_5678_ == 0 {
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5666_);
                    v_as_x27_5652_ = v_tail_5660_;
                    v_b_5653_ = v___x_5664_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___boxed(
    mut v_as_x27_5690_: *mut crate::leanh::LeanObject,
    mut v_b_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5695_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(
            v_as_x27_5690_,
            v_b_5691_,
            v___y_5692_,
            v___y_5693_,
        );
    crate::leanh::lean_dec(v___y_5693_);
    crate::leanh::lean_dec_ref(v___y_5692_);
    crate::leanh::lean_dec(v_as_x27_5690_);
    return v_res_5695_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5697_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0;
    v___x_5698_ = l_Lean_stringToMessageData(v___x_5697_);
    return v___x_5698_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(
    mut v_as_x27_5702_: *mut crate::leanh::LeanObject,
    mut v_b_5703_: *mut crate::leanh::LeanObject,
    mut v___y_5704_: *mut crate::leanh::LeanObject,
    mut v___y_5705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: u8 = 0;
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: u8 = 0;
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5702_) == 0 {
                    v___x_5707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5707_, 0, v_b_5703_);
                    return v___x_5707_;
                } else {
                    v_head_5708_ = crate::leanh::lean_ctor_get(v_as_x27_5702_, 0);
                    v_snd_5709_ = crate::leanh::lean_ctor_get(v_head_5708_, 1);
                    v_tail_5710_ = crate::leanh::lean_ctor_get(v_as_x27_5702_, 1);
                    v_fst_5711_ = crate::leanh::lean_ctor_get(v_head_5708_, 0);
                    v_fst_5712_ = crate::leanh::lean_ctor_get(v_snd_5709_, 0);
                    v_snd_5713_ = crate::leanh::lean_ctor_get(v_snd_5709_, 1);
                    v___x_5714_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_fst_5712_) == 1 {
                        v_str_5715_ = crate::leanh::lean_ctor_get(v_fst_5712_, 1);
                        crate::leanh::lean_inc_ref(v_str_5715_);
                        v___x_5716_ = l_Lean_Linter_List_stripBinderName(v_str_5715_);
                        v___x_5717_ = l_Lean_Linter_List_allowedListNames;
                        v___x_5718_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5716_,
                            v___x_5717_,
                        );
                        if v___x_5718_ == 0 {
                            v___x_5719_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5733_ = l_Lean_Expr_getAppNumArgs(v_snd_5713_);
                            v___x_5734_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5735_ = lean_nat_sub(v___x_5733_, v___x_5734_);
                            crate::leanh::lean_dec(v___x_5733_);
                            v___x_5736_ = l_Lean_Expr_getRevArg_x21(v_snd_5713_, v___x_5735_);
                            v___x_5737_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3;
                            v___x_5738_ = l_Lean_Expr_isAppOf(v___x_5736_, v___x_5737_);
                            if v___x_5738_ == 0 {
                                v___x_5739_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                                v___x_5740_ = l_Lean_Expr_isAppOf(v___x_5736_, v___x_5739_);
                                crate::leanh::lean_dec_ref(v___x_5736_);
                                if v___x_5740_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5736_);
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5716_);
                            v_as_x27_5702_ = v_tail_5710_;
                            v_b_5703_ = v___x_5714_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_5702_ = v_tail_5710_;
                        v_b_5703_ = v___x_5714_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5721_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
                v___x_5722_ = l_Lean_stringToMessageData(v___x_5716_);
                v___x_5723_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5723_, 0, v___x_5721_);
                crate::leanh::lean_ctor_set(v___x_5723_, 1, v___x_5722_);
                v___x_5724_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5719_,
                    v_fst_5711_,
                    v___x_5723_,
                    v___y_5704_,
                    v___y_5705_,
                );
                if crate::leanh::lean_obj_tag(v___x_5724_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5724_, 1);
                    v_as_x27_5702_ = v_tail_5710_;
                    v_b_5703_ = v___x_5714_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5724_;
                }
            }
            2 => {
                v___x_5727_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2;
                v___x_5728_ = lean_string_dec_eq(v___x_5716_, v___x_5727_);
                if v___x_5728_ == 0 {
                    v___x_5729_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2;
                    v___x_5730_ = lean_string_dec_eq(v___x_5716_, v___x_5729_);
                    if v___x_5730_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5716_);
                        v_as_x27_5702_ = v_tail_5710_;
                        v_b_5703_ = v___x_5714_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5716_);
                    v_as_x27_5702_ = v_tail_5710_;
                    v_b_5703_ = v___x_5714_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___boxed(
    mut v_as_x27_5743_: *mut crate::leanh::LeanObject,
    mut v_b_5744_: *mut crate::leanh::LeanObject,
    mut v___y_5745_: *mut crate::leanh::LeanObject,
    mut v___y_5746_: *mut crate::leanh::LeanObject,
    mut v___y_5747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(
            v_as_x27_5743_,
            v_b_5744_,
            v___y_5745_,
            v___y_5746_,
        );
    crate::leanh::lean_dec(v___y_5746_);
    crate::leanh::lean_dec_ref(v___y_5745_);
    crate::leanh::lean_dec(v_as_x27_5743_);
    return v_res_5748_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(
    mut v_a_5749_: *mut crate::leanh::LeanObject,
    mut v_a_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5757_: u8 = 0;
    let mut v_snd_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_unused_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5749_) == 0 {
                    v___x_5751_ = l_List_reverse___redArg(v_a_5750_);
                    return v___x_5751_;
                } else {
                    v_head_5752_ = crate::leanh::lean_ctor_get(v_a_5749_, 0);
                    crate::leanh::lean_inc(v_head_5752_);
                    v_snd_5753_ = crate::leanh::lean_ctor_get(v_head_5752_, 1);
                    v_tail_5754_ = crate::leanh::lean_ctor_get(v_a_5749_, 1);
                    v_isSharedCheck_5766_ = (!crate::leanh::lean_is_exclusive(v_a_5749_)) as u8;
                    if v_isSharedCheck_5766_ == 0 {
                        v_unused_5767_ = crate::leanh::lean_ctor_get(v_a_5749_, 0);
                        crate::leanh::lean_dec(v_unused_5767_);
                        v___x_5756_ = v_a_5749_;
                        v_isShared_5757_ = v_isSharedCheck_5766_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5754_);
                        crate::leanh::lean_dec(v_a_5749_);
                        v___x_5756_ = crate::leanh::lean_box(0);
                        v_isShared_5757_ = v_isSharedCheck_5766_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5758_ = crate::leanh::lean_ctor_get(v_snd_5753_, 1);
                v___x_5759_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                v___x_5760_ = l_Lean_Expr_isAppOf(v_snd_5758_, v___x_5759_);
                if v___x_5760_ == 0 {
                    crate::leanh::lean_del_object(v___x_5756_);
                    crate::leanh::lean_dec(v_head_5752_);
                    v_a_5749_ = v_tail_5754_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5757_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5756_, 1, v_a_5750_);
                        v___x_5763_ = v___x_5756_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_head_5752_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 1, v_a_5750_);
                        v___x_5763_ = v_reuseFailAlloc_5765_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5749_ = v_tail_5754_;
                v_a_5750_ = v___x_5763_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(
    mut v___x_5768_: u8,
    mut v_x_5769_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___x_5768_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(
    mut v___x_5770_: *mut crate::leanh::LeanObject,
    mut v_x_5771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16026__boxed_5772_: u8 = 0;
    let mut v_res_5773_: u8 = 0;
    let mut v_r_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16026__boxed_5772_ = (crate::leanh::lean_unbox(v___x_5770_) as u8);
    v_res_5773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v___x_16026__boxed_5772_, v_x_5771_);
    crate::leanh::lean_dec_ref(v_x_5771_);
    v_r_5774_ = crate::leanh::lean_box((v_res_5773_) as usize);
    return v_r_5774_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(
    mut v_a_5775_: *mut crate::leanh::LeanObject,
    mut v_a_5776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v_snd_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut v_unused_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5775_) == 0 {
                    v___x_5777_ = l_List_reverse___redArg(v_a_5776_);
                    return v___x_5777_;
                } else {
                    v_head_5778_ = crate::leanh::lean_ctor_get(v_a_5775_, 0);
                    crate::leanh::lean_inc(v_head_5778_);
                    v_snd_5779_ = crate::leanh::lean_ctor_get(v_head_5778_, 1);
                    v_tail_5780_ = crate::leanh::lean_ctor_get(v_a_5775_, 1);
                    v_isSharedCheck_5792_ = (!crate::leanh::lean_is_exclusive(v_a_5775_)) as u8;
                    if v_isSharedCheck_5792_ == 0 {
                        v_unused_5793_ = crate::leanh::lean_ctor_get(v_a_5775_, 0);
                        crate::leanh::lean_dec(v_unused_5793_);
                        v___x_5782_ = v_a_5775_;
                        v_isShared_5783_ = v_isSharedCheck_5792_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5780_);
                        crate::leanh::lean_dec(v_a_5775_);
                        v___x_5782_ = crate::leanh::lean_box(0);
                        v_isShared_5783_ = v_isSharedCheck_5792_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5784_ = crate::leanh::lean_ctor_get(v_snd_5779_, 1);
                v___x_5785_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3;
                v___x_5786_ = l_Lean_Expr_isAppOf(v_snd_5784_, v___x_5785_);
                if v___x_5786_ == 0 {
                    crate::leanh::lean_del_object(v___x_5782_);
                    crate::leanh::lean_dec(v_head_5778_);
                    v_a_5775_ = v_tail_5780_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5783_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5782_, 1, v_a_5776_);
                        v___x_5789_ = v___x_5782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5791_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_head_5778_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_a_5776_);
                        v___x_5789_ = v_reuseFailAlloc_5791_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5775_ = v_tail_5780_;
                v_a_5776_ = v___x_5789_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0;
    v___x_5796_ = l_Lean_stringToMessageData(v___x_5795_);
    return v___x_5796_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(
    mut v_as_x27_5797_: *mut crate::leanh::LeanObject,
    mut v_b_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: u8 = 0;
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5797_) == 0 {
                    v___x_5802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5802_, 0, v_b_5798_);
                    return v___x_5802_;
                } else {
                    v_head_5803_ = crate::leanh::lean_ctor_get(v_as_x27_5797_, 0);
                    v_snd_5804_ = crate::leanh::lean_ctor_get(v_head_5803_, 1);
                    v_tail_5805_ = crate::leanh::lean_ctor_get(v_as_x27_5797_, 1);
                    v_fst_5806_ = crate::leanh::lean_ctor_get(v_head_5803_, 0);
                    v_fst_5807_ = crate::leanh::lean_ctor_get(v_snd_5804_, 0);
                    v_snd_5808_ = crate::leanh::lean_ctor_get(v_snd_5804_, 1);
                    v___x_5809_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_fst_5807_) == 1 {
                        v_str_5810_ = crate::leanh::lean_ctor_get(v_fst_5807_, 1);
                        crate::leanh::lean_inc_ref(v_str_5810_);
                        v___x_5811_ = l_Lean_Linter_List_stripBinderName(v_str_5810_);
                        v___x_5812_ = l_Lean_Linter_List_allowedVectorNames;
                        v___x_5813_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5811_,
                            v___x_5812_,
                        );
                        if v___x_5813_ == 0 {
                            v___x_5814_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5821_ = l_Lean_Expr_getAppNumArgs(v_snd_5808_);
                            v___x_5822_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5823_ = lean_nat_sub(v___x_5821_, v___x_5822_);
                            crate::leanh::lean_dec(v___x_5821_);
                            v___x_5824_ = l_Lean_Expr_getRevArg_x21(v_snd_5808_, v___x_5823_);
                            v___x_5825_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                            v___x_5826_ = l_Lean_Expr_isAppOf(v___x_5824_, v___x_5825_);
                            crate::leanh::lean_dec_ref(v___x_5824_);
                            if v___x_5826_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_5827_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2;
                                v___x_5828_ = lean_string_dec_eq(v___x_5811_, v___x_5827_);
                                if v___x_5828_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5811_);
                                    v_as_x27_5797_ = v_tail_5805_;
                                    v_b_5798_ = v___x_5809_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5811_);
                            v_as_x27_5797_ = v_tail_5805_;
                            v_b_5798_ = v___x_5809_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_5797_ = v_tail_5805_;
                        v_b_5798_ = v___x_5809_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
                v___x_5817_ = l_Lean_stringToMessageData(v___x_5811_);
                v___x_5818_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5818_, 0, v___x_5816_);
                crate::leanh::lean_ctor_set(v___x_5818_, 1, v___x_5817_);
                v___x_5819_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5814_,
                    v_fst_5806_,
                    v___x_5818_,
                    v___y_5799_,
                    v___y_5800_,
                );
                if crate::leanh::lean_obj_tag(v___x_5819_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5819_, 1);
                    v_as_x27_5797_ = v_tail_5805_;
                    v_b_5798_ = v___x_5809_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5819_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___boxed(
    mut v_as_x27_5832_: *mut crate::leanh::LeanObject,
    mut v_b_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5837_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(
            v_as_x27_5832_,
            v_b_5833_,
            v___y_5834_,
            v___y_5835_,
        );
    crate::leanh::lean_dec(v___y_5835_);
    crate::leanh::lean_dec_ref(v___y_5834_);
    crate::leanh::lean_dec(v_as_x27_5832_);
    return v_res_5837_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(
    mut v_a_5838_: *mut crate::leanh::LeanObject,
    mut v_a_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v_snd_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_unused_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5838_) == 0 {
                    v___x_5840_ = l_List_reverse___redArg(v_a_5839_);
                    return v___x_5840_;
                } else {
                    v_head_5841_ = crate::leanh::lean_ctor_get(v_a_5838_, 0);
                    crate::leanh::lean_inc(v_head_5841_);
                    v_snd_5842_ = crate::leanh::lean_ctor_get(v_head_5841_, 1);
                    v_tail_5843_ = crate::leanh::lean_ctor_get(v_a_5838_, 1);
                    v_isSharedCheck_5855_ = (!crate::leanh::lean_is_exclusive(v_a_5838_)) as u8;
                    if v_isSharedCheck_5855_ == 0 {
                        v_unused_5856_ = crate::leanh::lean_ctor_get(v_a_5838_, 0);
                        crate::leanh::lean_dec(v_unused_5856_);
                        v___x_5845_ = v_a_5838_;
                        v_isShared_5846_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5843_);
                        crate::leanh::lean_dec(v_a_5838_);
                        v___x_5845_ = crate::leanh::lean_box(0);
                        v_isShared_5846_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5847_ = crate::leanh::lean_ctor_get(v_snd_5842_, 1);
                v___x_5848_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                v___x_5849_ = l_Lean_Expr_isAppOf(v_snd_5847_, v___x_5848_);
                if v___x_5849_ == 0 {
                    crate::leanh::lean_del_object(v___x_5845_);
                    crate::leanh::lean_dec(v_head_5841_);
                    v_a_5838_ = v_tail_5843_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5845_, 1, v_a_5839_);
                        v___x_5852_ = v___x_5845_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_head_5841_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_a_5839_);
                        v___x_5852_ = v_reuseFailAlloc_5854_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5838_ = v_tail_5843_;
                v_a_5839_ = v___x_5852_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(
    mut v___x_5857_: u8,
    mut v_as_5858_: *mut crate::leanh::LeanObject,
    mut v_sz_5859_: usize,
    mut v_i_5860_: usize,
    mut v_b_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5865_: u8 = 0;
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: usize = 0;
    let mut v___x_5882_: usize = 0;
    let mut v_a_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut v_a_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5899_: u8 = 0;
    let mut v_a_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5907_: u8 = 0;
    let mut v_a_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v_ref_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5865_ = lean_usize_dec_lt(v_i_5860_, v_sz_5859_);
                if v___x_5865_ == 0 {
                    v___x_5866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5866_, 0, v_b_5861_);
                    return v___x_5866_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5861_);
                    v___x_5867_ = crate::leanh::lean_box((v___x_5857_) as usize);
                    v___f_5868_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_5868_, 0, v___x_5867_);
                    v_a_5869_ = lean_array_uget_borrowed(v_as_5858_, v_i_5860_);
                    crate::leanh::lean_inc(v_a_5869_);
                    v___x_5870_ = l_Lean_Linter_List_binders(v_a_5869_, v___f_5868_);
                    if crate::leanh::lean_obj_tag(v___x_5870_) == 0 {
                        v_a_5871_ = crate::leanh::lean_ctor_get(v___x_5870_, 0);
                        crate::leanh::lean_inc_n(v_a_5871_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5870_, 1);
                        v___x_5872_ = crate::leanh::lean_box(0);
                        v___x_5873_ = crate::leanh::lean_box(0);
                        v___x_5874_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_5871_, v___x_5873_);
                        v___x_5875_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_5874_, v___x_5872_, v___y_5862_, v___y_5863_);
                        crate::leanh::lean_dec(v___x_5874_);
                        if crate::leanh::lean_obj_tag(v___x_5875_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5875_, 1);
                            crate::leanh::lean_inc(v_a_5871_);
                            v___x_5876_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_5871_, v___x_5873_);
                            v___x_5877_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_5876_, v___x_5872_, v___y_5862_, v___y_5863_);
                            crate::leanh::lean_dec(v___x_5876_);
                            if crate::leanh::lean_obj_tag(v___x_5877_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5877_, 1);
                                v___x_5878_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_5871_, v___x_5873_);
                                v___x_5879_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_5878_, v___x_5872_, v___y_5862_, v___y_5863_);
                                crate::leanh::lean_dec(v___x_5878_);
                                if crate::leanh::lean_obj_tag(v___x_5879_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5879_, 1);
                                    v___x_5880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                    v___x_5881_ = 1usize;
                                    v___x_5882_ = lean_usize_add(v_i_5860_, v___x_5881_);
                                    v_i_5860_ = v___x_5882_;
                                    v_b_5861_ = v___x_5880_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_a_5884_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                                    v_isSharedCheck_5891_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                                    if v_isSharedCheck_5891_ == 0 {
                                        v___x_5886_ = v___x_5879_;
                                        v_isShared_5887_ = v_isSharedCheck_5891_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5884_);
                                        crate::leanh::lean_dec(v___x_5879_);
                                        v___x_5886_ = crate::leanh::lean_box(0);
                                        v_isShared_5887_ = v_isSharedCheck_5891_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5871_);
                                v_a_5892_ = crate::leanh::lean_ctor_get(v___x_5877_, 0);
                                v_isSharedCheck_5899_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5877_)) as u8;
                                if v_isSharedCheck_5899_ == 0 {
                                    v___x_5894_ = v___x_5877_;
                                    v_isShared_5895_ = v_isSharedCheck_5899_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5892_);
                                    crate::leanh::lean_dec(v___x_5877_);
                                    v___x_5894_ = crate::leanh::lean_box(0);
                                    v_isShared_5895_ = v_isSharedCheck_5899_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5871_);
                            v_a_5900_ = crate::leanh::lean_ctor_get(v___x_5875_, 0);
                            v_isSharedCheck_5907_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5875_)) as u8;
                            if v_isSharedCheck_5907_ == 0 {
                                v___x_5902_ = v___x_5875_;
                                v_isShared_5903_ = v_isSharedCheck_5907_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5900_);
                                crate::leanh::lean_dec(v___x_5875_);
                                v___x_5902_ = crate::leanh::lean_box(0);
                                v_isShared_5903_ = v_isSharedCheck_5907_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_5908_ = crate::leanh::lean_ctor_get(v___x_5870_, 0);
                        v_isSharedCheck_5920_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5870_)) as u8;
                        if v_isSharedCheck_5920_ == 0 {
                            v___x_5910_ = v___x_5870_;
                            v_isShared_5911_ = v_isSharedCheck_5920_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5908_);
                            crate::leanh::lean_dec(v___x_5870_);
                            v___x_5910_ = crate::leanh::lean_box(0);
                            v_isShared_5911_ = v_isSharedCheck_5920_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5887_ == 0 {
                    v___x_5889_ = v___x_5886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
                    v___x_5889_ = v_reuseFailAlloc_5890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5889_;
            }
            3 => {
                if v_isShared_5895_ == 0 {
                    v___x_5897_ = v___x_5894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
                    v___x_5897_ = v_reuseFailAlloc_5898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5897_;
            }
            5 => {
                if v_isShared_5903_ == 0 {
                    v___x_5905_ = v___x_5902_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
                    v___x_5905_ = v_reuseFailAlloc_5906_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5905_;
            }
            7 => {
                v_ref_5912_ = crate::leanh::lean_ctor_get(v___y_5862_, 7);
                v___x_5913_ = lean_io_error_to_string(v_a_5908_);
                v___x_5914_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5914_, 0, v___x_5913_);
                v___x_5915_ = l_Lean_MessageData_ofFormat(v___x_5914_);
                crate::leanh::lean_inc(v_ref_5912_);
                v___x_5916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5916_, 0, v_ref_5912_);
                crate::leanh::lean_ctor_set(v___x_5916_, 1, v___x_5915_);
                if v_isShared_5911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5910_, 0, v___x_5916_);
                    v___x_5918_ = v___x_5910_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5919_, 0, v___x_5916_);
                    v___x_5918_ = v_reuseFailAlloc_5919_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9___boxed(
    mut v___x_5921_: *mut crate::leanh::LeanObject,
    mut v_as_5922_: *mut crate::leanh::LeanObject,
    mut v_sz_5923_: *mut crate::leanh::LeanObject,
    mut v_i_5924_: *mut crate::leanh::LeanObject,
    mut v_b_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16206__boxed_5929_: u8 = 0;
    let mut v_sz_boxed_5930_: usize = 0;
    let mut v_i_boxed_5931_: usize = 0;
    let mut v_res_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16206__boxed_5929_ = (crate::leanh::lean_unbox(v___x_5921_) as u8);
    v_sz_boxed_5930_ = crate::leanh::lean_unbox_usize(v_sz_5923_);
    crate::leanh::lean_dec(v_sz_5923_);
    v_i_boxed_5931_ = crate::leanh::lean_unbox_usize(v_i_5924_);
    crate::leanh::lean_dec(v_i_5924_);
    v_res_5932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_16206__boxed_5929_, v_as_5922_, v_sz_boxed_5930_, v_i_boxed_5931_, v_b_5925_, v___y_5926_, v___y_5927_);
    crate::leanh::lean_dec(v___y_5927_);
    crate::leanh::lean_dec_ref(v___y_5926_);
    crate::leanh::lean_dec_ref(v_as_5922_);
    return v_res_5932_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(
    mut v___x_5933_: u8,
    mut v_as_5934_: *mut crate::leanh::LeanObject,
    mut v_sz_5935_: usize,
    mut v_i_5936_: usize,
    mut v_b_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
    mut v___y_5939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5941_: u8 = 0;
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: usize = 0;
    let mut v___x_5958_: usize = 0;
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_a_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_a_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v_ref_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5941_ = lean_usize_dec_lt(v_i_5936_, v_sz_5935_);
                if v___x_5941_ == 0 {
                    v___x_5942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5942_, 0, v_b_5937_);
                    return v___x_5942_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5937_);
                    v___x_5943_ = crate::leanh::lean_box((v___x_5933_) as usize);
                    v___f_5944_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_5944_, 0, v___x_5943_);
                    v_a_5945_ = lean_array_uget_borrowed(v_as_5934_, v_i_5936_);
                    crate::leanh::lean_inc(v_a_5945_);
                    v___x_5946_ = l_Lean_Linter_List_binders(v_a_5945_, v___f_5944_);
                    if crate::leanh::lean_obj_tag(v___x_5946_) == 0 {
                        v_a_5947_ = crate::leanh::lean_ctor_get(v___x_5946_, 0);
                        crate::leanh::lean_inc_n(v_a_5947_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5946_, 1);
                        v___x_5948_ = crate::leanh::lean_box(0);
                        v___x_5949_ = crate::leanh::lean_box(0);
                        v___x_5950_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_5947_, v___x_5949_);
                        v___x_5951_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_5950_, v___x_5948_, v___y_5938_, v___y_5939_);
                        crate::leanh::lean_dec(v___x_5950_);
                        if crate::leanh::lean_obj_tag(v___x_5951_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5951_, 1);
                            crate::leanh::lean_inc(v_a_5947_);
                            v___x_5952_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_5947_, v___x_5949_);
                            v___x_5953_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_5952_, v___x_5948_, v___y_5938_, v___y_5939_);
                            crate::leanh::lean_dec(v___x_5952_);
                            if crate::leanh::lean_obj_tag(v___x_5953_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5953_, 1);
                                v___x_5954_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_5947_, v___x_5949_);
                                v___x_5955_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_5954_, v___x_5948_, v___y_5938_, v___y_5939_);
                                crate::leanh::lean_dec(v___x_5954_);
                                if crate::leanh::lean_obj_tag(v___x_5955_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5955_, 1);
                                    v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                    v___x_5957_ = 1usize;
                                    v___x_5958_ = lean_usize_add(v_i_5936_, v___x_5957_);
                                    v___x_5959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_5933_, v_as_5934_, v_sz_5935_, v___x_5958_, v___x_5956_, v___y_5938_, v___y_5939_);
                                    return v___x_5959_;
                                } else {
                                    v_a_5960_ = crate::leanh::lean_ctor_get(v___x_5955_, 0);
                                    v_isSharedCheck_5967_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5955_)) as u8;
                                    if v_isSharedCheck_5967_ == 0 {
                                        v___x_5962_ = v___x_5955_;
                                        v_isShared_5963_ = v_isSharedCheck_5967_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5960_);
                                        crate::leanh::lean_dec(v___x_5955_);
                                        v___x_5962_ = crate::leanh::lean_box(0);
                                        v_isShared_5963_ = v_isSharedCheck_5967_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5947_);
                                v_a_5968_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                                v_isSharedCheck_5975_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                                if v_isSharedCheck_5975_ == 0 {
                                    v___x_5970_ = v___x_5953_;
                                    v_isShared_5971_ = v_isSharedCheck_5975_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5968_);
                                    crate::leanh::lean_dec(v___x_5953_);
                                    v___x_5970_ = crate::leanh::lean_box(0);
                                    v_isShared_5971_ = v_isSharedCheck_5975_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5947_);
                            v_a_5976_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                            v_isSharedCheck_5983_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                            if v_isSharedCheck_5983_ == 0 {
                                v___x_5978_ = v___x_5951_;
                                v_isShared_5979_ = v_isSharedCheck_5983_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5976_);
                                crate::leanh::lean_dec(v___x_5951_);
                                v___x_5978_ = crate::leanh::lean_box(0);
                                v_isShared_5979_ = v_isSharedCheck_5983_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_5984_ = crate::leanh::lean_ctor_get(v___x_5946_, 0);
                        v_isSharedCheck_5996_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5946_)) as u8;
                        if v_isSharedCheck_5996_ == 0 {
                            v___x_5986_ = v___x_5946_;
                            v_isShared_5987_ = v_isSharedCheck_5996_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5984_);
                            crate::leanh::lean_dec(v___x_5946_);
                            v___x_5986_ = crate::leanh::lean_box(0);
                            v_isShared_5987_ = v_isSharedCheck_5996_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5963_ == 0 {
                    v___x_5965_ = v___x_5962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_a_5960_);
                    v___x_5965_ = v_reuseFailAlloc_5966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5965_;
            }
            3 => {
                if v_isShared_5971_ == 0 {
                    v___x_5973_ = v___x_5970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_a_5968_);
                    v___x_5973_ = v_reuseFailAlloc_5974_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5973_;
            }
            5 => {
                if v_isShared_5979_ == 0 {
                    v___x_5981_ = v___x_5978_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5976_);
                    v___x_5981_ = v_reuseFailAlloc_5982_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5981_;
            }
            7 => {
                v_ref_5988_ = crate::leanh::lean_ctor_get(v___y_5938_, 7);
                v___x_5989_ = lean_io_error_to_string(v_a_5984_);
                v___x_5990_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5990_, 0, v___x_5989_);
                v___x_5991_ = l_Lean_MessageData_ofFormat(v___x_5990_);
                crate::leanh::lean_inc(v_ref_5988_);
                v___x_5992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5992_, 0, v_ref_5988_);
                crate::leanh::lean_ctor_set(v___x_5992_, 1, v___x_5991_);
                if v_isShared_5987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5986_, 0, v___x_5992_);
                    v___x_5994_ = v___x_5986_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5992_);
                    v___x_5994_ = v_reuseFailAlloc_5995_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8___boxed(
    mut v___x_5997_: *mut crate::leanh::LeanObject,
    mut v_as_5998_: *mut crate::leanh::LeanObject,
    mut v_sz_5999_: *mut crate::leanh::LeanObject,
    mut v_i_6000_: *mut crate::leanh::LeanObject,
    mut v_b_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16333__boxed_6005_: u8 = 0;
    let mut v_sz_boxed_6006_: usize = 0;
    let mut v_i_boxed_6007_: usize = 0;
    let mut v_res_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16333__boxed_6005_ = (crate::leanh::lean_unbox(v___x_5997_) as u8);
    v_sz_boxed_6006_ = crate::leanh::lean_unbox_usize(v_sz_5999_);
    crate::leanh::lean_dec(v_sz_5999_);
    v_i_boxed_6007_ = crate::leanh::lean_unbox_usize(v_i_6000_);
    crate::leanh::lean_dec(v_i_6000_);
    v_res_6008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_16333__boxed_6005_, v_as_5998_, v_sz_boxed_6006_, v_i_boxed_6007_, v_b_6001_, v___y_6002_, v___y_6003_);
    crate::leanh::lean_dec(v___y_6003_);
    crate::leanh::lean_dec_ref(v___y_6002_);
    crate::leanh::lean_dec_ref(v_as_5998_);
    return v_res_6008_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(
    mut v_init_6009_: *mut crate::leanh::LeanObject,
    mut v___x_6010_: u8,
    mut v_n_6011_: *mut crate::leanh::LeanObject,
    mut v_b_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6019_: usize = 0;
    let mut v___x_6020_: usize = 0;
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6025_: u8 = 0;
    let mut v_fst_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v_vs_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6048_: usize = 0;
    let mut v___x_6049_: usize = 0;
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v_fst_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_6011_) == 0 {
                    v_cs_6016_ = crate::leanh::lean_ctor_get(v_n_6011_, 0);
                    v___x_6017_ = crate::leanh::lean_box(0);
                    v___x_6018_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6018_, 0, v___x_6017_);
                    crate::leanh::lean_ctor_set(v___x_6018_, 1, v_b_6012_);
                    v_sz_6019_ = lean_array_size(v_cs_6016_);
                    v___x_6020_ = 0usize;
                    v___x_6021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_6009_, v___x_6010_, v_cs_6016_, v_sz_6019_, v___x_6020_, v___x_6018_, v___y_6013_, v___y_6014_);
                    if crate::leanh::lean_obj_tag(v___x_6021_) == 0 {
                        v_a_6022_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
                        v_isSharedCheck_6036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6021_)) as u8;
                        if v_isSharedCheck_6036_ == 0 {
                            v___x_6024_ = v___x_6021_;
                            v_isShared_6025_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6022_);
                            crate::leanh::lean_dec(v___x_6021_);
                            v___x_6024_ = crate::leanh::lean_box(0);
                            v_isShared_6025_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6037_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
                        v_isSharedCheck_6044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6021_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6039_ = v___x_6021_;
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6037_);
                            crate::leanh::lean_dec(v___x_6021_);
                            v___x_6039_ = crate::leanh::lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6045_ = crate::leanh::lean_ctor_get(v_n_6011_, 0);
                    v___x_6046_ = crate::leanh::lean_box(0);
                    v___x_6047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6047_, 0, v___x_6046_);
                    crate::leanh::lean_ctor_set(v___x_6047_, 1, v_b_6012_);
                    v_sz_6048_ = lean_array_size(v_vs_6045_);
                    v___x_6049_ = 0usize;
                    v___x_6050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_6010_, v_vs_6045_, v_sz_6048_, v___x_6049_, v___x_6047_, v___y_6013_, v___y_6014_);
                    if crate::leanh::lean_obj_tag(v___x_6050_) == 0 {
                        v_a_6051_ = crate::leanh::lean_ctor_get(v___x_6050_, 0);
                        v_isSharedCheck_6065_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6050_)) as u8;
                        if v_isSharedCheck_6065_ == 0 {
                            v___x_6053_ = v___x_6050_;
                            v_isShared_6054_ = v_isSharedCheck_6065_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6051_);
                            crate::leanh::lean_dec(v___x_6050_);
                            v___x_6053_ = crate::leanh::lean_box(0);
                            v_isShared_6054_ = v_isSharedCheck_6065_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6050_, 0);
                        v_isSharedCheck_6073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6050_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6050_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6066_);
                            crate::leanh::lean_dec(v___x_6050_);
                            v___x_6068_ = crate::leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6026_ = crate::leanh::lean_ctor_get(v_a_6022_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6026_) == 0 {
                    v_snd_6027_ = crate::leanh::lean_ctor_get(v_a_6022_, 1);
                    crate::leanh::lean_inc(v_snd_6027_);
                    crate::leanh::lean_dec(v_a_6022_);
                    v___x_6028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6028_, 0, v_snd_6027_);
                    if v_isShared_6025_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6024_, 0, v___x_6028_);
                        v___x_6030_ = v___x_6024_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6028_);
                        v___x_6030_ = v_reuseFailAlloc_6031_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6026_);
                    crate::leanh::lean_dec(v_a_6022_);
                    v_val_6032_ = crate::leanh::lean_ctor_get(v_fst_6026_, 0);
                    crate::leanh::lean_inc(v_val_6032_);
                    crate::leanh::lean_dec_ref_known(v_fst_6026_, 1);
                    if v_isShared_6025_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6024_, 0, v_val_6032_);
                        v___x_6034_ = v___x_6024_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_val_6032_);
                        v___x_6034_ = v_reuseFailAlloc_6035_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6030_;
            }
            3 => {
                return v___x_6034_;
            }
            4 => {
                if v_isShared_6040_ == 0 {
                    v___x_6042_ = v___x_6039_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6042_;
            }
            6 => {
                v_fst_6055_ = crate::leanh::lean_ctor_get(v_a_6051_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6055_) == 0 {
                    v_snd_6056_ = crate::leanh::lean_ctor_get(v_a_6051_, 1);
                    crate::leanh::lean_inc(v_snd_6056_);
                    crate::leanh::lean_dec(v_a_6051_);
                    v___x_6057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6057_, 0, v_snd_6056_);
                    if v_isShared_6054_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6053_, 0, v___x_6057_);
                        v___x_6059_ = v___x_6053_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6060_, 0, v___x_6057_);
                        v___x_6059_ = v_reuseFailAlloc_6060_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6055_);
                    crate::leanh::lean_dec(v_a_6051_);
                    v_val_6061_ = crate::leanh::lean_ctor_get(v_fst_6055_, 0);
                    crate::leanh::lean_inc(v_val_6061_);
                    crate::leanh::lean_dec_ref_known(v_fst_6055_, 1);
                    if v_isShared_6054_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6053_, 0, v_val_6061_);
                        v___x_6063_ = v___x_6053_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6064_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_val_6061_);
                        v___x_6063_ = v_reuseFailAlloc_6064_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6059_;
            }
            8 => {
                return v___x_6063_;
            }
            9 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(
    mut v_init_6074_: *mut crate::leanh::LeanObject,
    mut v___x_6075_: u8,
    mut v_as_6076_: *mut crate::leanh::LeanObject,
    mut v_sz_6077_: usize,
    mut v_i_6078_: usize,
    mut v_b_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6083_: u8 = 0;
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6088_: u8 = 0;
    let mut v_a_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: usize = 0;
    let mut v_reuseFailAlloc_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6110_: u8 = 0;
    let mut v_a_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6118_: u8 = 0;
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6083_ = lean_usize_dec_lt(v_i_6078_, v_sz_6077_);
                if v___x_6083_ == 0 {
                    v___x_6084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6084_, 0, v_b_6079_);
                    return v___x_6084_;
                } else {
                    v_snd_6085_ = crate::leanh::lean_ctor_get(v_b_6079_, 1);
                    v_isSharedCheck_6119_ = (!crate::leanh::lean_is_exclusive(v_b_6079_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v_unused_6120_ = crate::leanh::lean_ctor_get(v_b_6079_, 0);
                        crate::leanh::lean_dec(v_unused_6120_);
                        v___x_6087_ = v_b_6079_;
                        v_isShared_6088_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6085_);
                        crate::leanh::lean_dec(v_b_6079_);
                        v___x_6087_ = crate::leanh::lean_box(0);
                        v_isShared_6088_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6089_ = lean_array_uget_borrowed(v_as_6076_, v_i_6078_);
                crate::leanh::lean_inc(v_snd_6085_);
                v___x_6090_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6074_, v___x_6075_, v_a_6089_, v_snd_6085_, v___y_6080_, v___y_6081_);
                if crate::leanh::lean_obj_tag(v___x_6090_) == 0 {
                    v_a_6091_ = crate::leanh::lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6110_ = (!crate::leanh::lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6110_ == 0 {
                        v___x_6093_ = v___x_6090_;
                        v_isShared_6094_ = v_isSharedCheck_6110_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6091_);
                        crate::leanh::lean_dec(v___x_6090_);
                        v___x_6093_ = crate::leanh::lean_box(0);
                        v_isShared_6094_ = v_isSharedCheck_6110_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6087_);
                    crate::leanh::lean_dec(v_snd_6085_);
                    v_a_6111_ = crate::leanh::lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6118_ = (!crate::leanh::lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6118_ == 0 {
                        v___x_6113_ = v___x_6090_;
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6111_);
                        crate::leanh::lean_dec(v___x_6090_);
                        v___x_6113_ = crate::leanh::lean_box(0);
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6091_) == 0 {
                    v___x_6095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6095_, 0, v_a_6091_);
                    if v_isShared_6088_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6087_, 0, v___x_6095_);
                        v___x_6097_ = v___x_6087_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6101_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6095_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6101_, 1, v_snd_6085_);
                        v___x_6097_ = v_reuseFailAlloc_6101_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6093_);
                    crate::leanh::lean_dec(v_snd_6085_);
                    v_a_6102_ = crate::leanh::lean_ctor_get(v_a_6091_, 0);
                    crate::leanh::lean_inc(v_a_6102_);
                    crate::leanh::lean_dec_ref_known(v_a_6091_, 1);
                    v___x_6103_ = crate::leanh::lean_box(0);
                    if v_isShared_6088_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6087_, 1, v_a_6102_);
                        crate::leanh::lean_ctor_set(v___x_6087_, 0, v___x_6103_);
                        v___x_6105_ = v___x_6087_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6109_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6109_, 0, v___x_6103_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6109_, 1, v_a_6102_);
                        v___x_6105_ = v_reuseFailAlloc_6109_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6093_, 0, v___x_6097_);
                    v___x_6099_ = v___x_6093_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6097_);
                    v___x_6099_ = v_reuseFailAlloc_6100_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6099_;
            }
            5 => {
                v___x_6106_ = 1usize;
                v___x_6107_ = lean_usize_add(v_i_6078_, v___x_6106_);
                v_i_6078_ = v___x_6107_;
                v_b_6079_ = v___x_6105_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6114_ == 0 {
                    v___x_6116_ = v___x_6113_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
                    v___x_6116_ = v_reuseFailAlloc_6117_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7___boxed(
    mut v_init_6121_: *mut crate::leanh::LeanObject,
    mut v___x_6122_: *mut crate::leanh::LeanObject,
    mut v_as_6123_: *mut crate::leanh::LeanObject,
    mut v_sz_6124_: *mut crate::leanh::LeanObject,
    mut v_i_6125_: *mut crate::leanh::LeanObject,
    mut v_b_6126_: *mut crate::leanh::LeanObject,
    mut v___y_6127_: *mut crate::leanh::LeanObject,
    mut v___y_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16457__boxed_6130_: u8 = 0;
    let mut v_sz_boxed_6131_: usize = 0;
    let mut v_i_boxed_6132_: usize = 0;
    let mut v_res_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16457__boxed_6130_ = (crate::leanh::lean_unbox(v___x_6122_) as u8);
    v_sz_boxed_6131_ = crate::leanh::lean_unbox_usize(v_sz_6124_);
    crate::leanh::lean_dec(v_sz_6124_);
    v_i_boxed_6132_ = crate::leanh::lean_unbox_usize(v_i_6125_);
    crate::leanh::lean_dec(v_i_6125_);
    v_res_6133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_6121_, v___x_16457__boxed_6130_, v_as_6123_, v_sz_boxed_6131_, v_i_boxed_6132_, v_b_6126_, v___y_6127_, v___y_6128_);
    crate::leanh::lean_dec(v___y_6128_);
    crate::leanh::lean_dec_ref(v___y_6127_);
    crate::leanh::lean_dec_ref(v_as_6123_);
    return v_res_6133_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(
    mut v_init_6134_: *mut crate::leanh::LeanObject,
    mut v___x_6135_: *mut crate::leanh::LeanObject,
    mut v_n_6136_: *mut crate::leanh::LeanObject,
    mut v_b_6137_: *mut crate::leanh::LeanObject,
    mut v___y_6138_: *mut crate::leanh::LeanObject,
    mut v___y_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16477__boxed_6141_: u8 = 0;
    let mut v_res_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16477__boxed_6141_ = (crate::leanh::lean_unbox(v___x_6135_) as u8);
    v_res_6142_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6134_, v___x_16477__boxed_6141_, v_n_6136_, v_b_6137_, v___y_6138_, v___y_6139_);
    crate::leanh::lean_dec(v___y_6139_);
    crate::leanh::lean_dec_ref(v___y_6138_);
    crate::leanh::lean_dec_ref(v_n_6136_);
    return v_res_6142_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(
    mut v___x_6143_: u8,
    mut v_as_6144_: *mut crate::leanh::LeanObject,
    mut v_sz_6145_: usize,
    mut v_i_6146_: usize,
    mut v_b_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: usize = 0;
    let mut v___x_6168_: usize = 0;
    let mut v_a_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6173_: u8 = 0;
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6177_: u8 = 0;
    let mut v_a_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6181_: u8 = 0;
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_a_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut v_a_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v_ref_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6151_ = lean_usize_dec_lt(v_i_6146_, v_sz_6145_);
                if v___x_6151_ == 0 {
                    v___x_6152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6152_, 0, v_b_6147_);
                    return v___x_6152_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_6147_);
                    v___x_6153_ = crate::leanh::lean_box((v___x_6143_) as usize);
                    v___f_6154_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_6154_, 0, v___x_6153_);
                    v_a_6155_ = lean_array_uget_borrowed(v_as_6144_, v_i_6146_);
                    crate::leanh::lean_inc(v_a_6155_);
                    v___x_6156_ = l_Lean_Linter_List_binders(v_a_6155_, v___f_6154_);
                    if crate::leanh::lean_obj_tag(v___x_6156_) == 0 {
                        v_a_6157_ = crate::leanh::lean_ctor_get(v___x_6156_, 0);
                        crate::leanh::lean_inc_n(v_a_6157_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6156_, 1);
                        v___x_6158_ = crate::leanh::lean_box(0);
                        v___x_6159_ = crate::leanh::lean_box(0);
                        v___x_6160_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_6157_, v___x_6159_);
                        v___x_6161_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_6160_, v___x_6158_, v___y_6148_, v___y_6149_);
                        crate::leanh::lean_dec(v___x_6160_);
                        if crate::leanh::lean_obj_tag(v___x_6161_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6161_, 1);
                            crate::leanh::lean_inc(v_a_6157_);
                            v___x_6162_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_6157_, v___x_6159_);
                            v___x_6163_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_6162_, v___x_6158_, v___y_6148_, v___y_6149_);
                            crate::leanh::lean_dec(v___x_6162_);
                            if crate::leanh::lean_obj_tag(v___x_6163_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6163_, 1);
                                v___x_6164_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_6157_, v___x_6159_);
                                v___x_6165_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_6164_, v___x_6158_, v___y_6148_, v___y_6149_);
                                crate::leanh::lean_dec(v___x_6164_);
                                if crate::leanh::lean_obj_tag(v___x_6165_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6165_, 1);
                                    v___x_6166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                    v___x_6167_ = 1usize;
                                    v___x_6168_ = lean_usize_add(v_i_6146_, v___x_6167_);
                                    v_i_6146_ = v___x_6168_;
                                    v_b_6147_ = v___x_6166_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_a_6170_ = crate::leanh::lean_ctor_get(v___x_6165_, 0);
                                    v_isSharedCheck_6177_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6165_)) as u8;
                                    if v_isSharedCheck_6177_ == 0 {
                                        v___x_6172_ = v___x_6165_;
                                        v_isShared_6173_ = v_isSharedCheck_6177_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6170_);
                                        crate::leanh::lean_dec(v___x_6165_);
                                        v___x_6172_ = crate::leanh::lean_box(0);
                                        v_isShared_6173_ = v_isSharedCheck_6177_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6157_);
                                v_a_6178_ = crate::leanh::lean_ctor_get(v___x_6163_, 0);
                                v_isSharedCheck_6185_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6163_)) as u8;
                                if v_isSharedCheck_6185_ == 0 {
                                    v___x_6180_ = v___x_6163_;
                                    v_isShared_6181_ = v_isSharedCheck_6185_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6178_);
                                    crate::leanh::lean_dec(v___x_6163_);
                                    v___x_6180_ = crate::leanh::lean_box(0);
                                    v_isShared_6181_ = v_isSharedCheck_6185_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6157_);
                            v_a_6186_ = crate::leanh::lean_ctor_get(v___x_6161_, 0);
                            v_isSharedCheck_6193_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6161_)) as u8;
                            if v_isSharedCheck_6193_ == 0 {
                                v___x_6188_ = v___x_6161_;
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6186_);
                                crate::leanh::lean_dec(v___x_6161_);
                                v___x_6188_ = crate::leanh::lean_box(0);
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_6194_ = crate::leanh::lean_ctor_get(v___x_6156_, 0);
                        v_isSharedCheck_6206_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6156_)) as u8;
                        if v_isSharedCheck_6206_ == 0 {
                            v___x_6196_ = v___x_6156_;
                            v_isShared_6197_ = v_isSharedCheck_6206_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6194_);
                            crate::leanh::lean_dec(v___x_6156_);
                            v___x_6196_ = crate::leanh::lean_box(0);
                            v_isShared_6197_ = v_isSharedCheck_6206_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6173_ == 0 {
                    v___x_6175_ = v___x_6172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
                    v___x_6175_ = v_reuseFailAlloc_6176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6175_;
            }
            3 => {
                if v_isShared_6181_ == 0 {
                    v___x_6183_ = v___x_6180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6178_);
                    v___x_6183_ = v_reuseFailAlloc_6184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6183_;
            }
            5 => {
                if v_isShared_6189_ == 0 {
                    v___x_6191_ = v___x_6188_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6191_;
            }
            7 => {
                v_ref_6198_ = crate::leanh::lean_ctor_get(v___y_6148_, 7);
                v___x_6199_ = lean_io_error_to_string(v_a_6194_);
                v___x_6200_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6200_, 0, v___x_6199_);
                v___x_6201_ = l_Lean_MessageData_ofFormat(v___x_6200_);
                crate::leanh::lean_inc(v_ref_6198_);
                v___x_6202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6202_, 0, v_ref_6198_);
                crate::leanh::lean_ctor_set(v___x_6202_, 1, v___x_6201_);
                if v_isShared_6197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6196_, 0, v___x_6202_);
                    v___x_6204_ = v___x_6196_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6205_, 0, v___x_6202_);
                    v___x_6204_ = v_reuseFailAlloc_6205_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10___boxed(
    mut v___x_6207_: *mut crate::leanh::LeanObject,
    mut v_as_6208_: *mut crate::leanh::LeanObject,
    mut v_sz_6209_: *mut crate::leanh::LeanObject,
    mut v_i_6210_: *mut crate::leanh::LeanObject,
    mut v_b_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
    mut v___y_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16661__boxed_6215_: u8 = 0;
    let mut v_sz_boxed_6216_: usize = 0;
    let mut v_i_boxed_6217_: usize = 0;
    let mut v_res_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16661__boxed_6215_ = (crate::leanh::lean_unbox(v___x_6207_) as u8);
    v_sz_boxed_6216_ = crate::leanh::lean_unbox_usize(v_sz_6209_);
    crate::leanh::lean_dec(v_sz_6209_);
    v_i_boxed_6217_ = crate::leanh::lean_unbox_usize(v_i_6210_);
    crate::leanh::lean_dec(v_i_6210_);
    v_res_6218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_16661__boxed_6215_, v_as_6208_, v_sz_boxed_6216_, v_i_boxed_6217_, v_b_6211_, v___y_6212_, v___y_6213_);
    crate::leanh::lean_dec(v___y_6213_);
    crate::leanh::lean_dec_ref(v___y_6212_);
    crate::leanh::lean_dec_ref(v_as_6208_);
    return v_res_6218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(
    mut v___x_6219_: u8,
    mut v_as_6220_: *mut crate::leanh::LeanObject,
    mut v_sz_6221_: usize,
    mut v_i_6222_: usize,
    mut v_b_6223_: *mut crate::leanh::LeanObject,
    mut v___y_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6227_: u8 = 0;
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: usize = 0;
    let mut v___x_6244_: usize = 0;
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6249_: u8 = 0;
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_a_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_a_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_a_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v_ref_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6227_ = lean_usize_dec_lt(v_i_6222_, v_sz_6221_);
                if v___x_6227_ == 0 {
                    v___x_6228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6228_, 0, v_b_6223_);
                    return v___x_6228_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_6223_);
                    v___x_6229_ = crate::leanh::lean_box((v___x_6219_) as usize);
                    v___f_6230_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_6230_, 0, v___x_6229_);
                    v_a_6231_ = lean_array_uget_borrowed(v_as_6220_, v_i_6222_);
                    crate::leanh::lean_inc(v_a_6231_);
                    v___x_6232_ = l_Lean_Linter_List_binders(v_a_6231_, v___f_6230_);
                    if crate::leanh::lean_obj_tag(v___x_6232_) == 0 {
                        v_a_6233_ = crate::leanh::lean_ctor_get(v___x_6232_, 0);
                        crate::leanh::lean_inc_n(v_a_6233_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6232_, 1);
                        v___x_6234_ = crate::leanh::lean_box(0);
                        v___x_6235_ = crate::leanh::lean_box(0);
                        v___x_6236_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_6233_, v___x_6235_);
                        v___x_6237_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_6236_, v___x_6234_, v___y_6224_, v___y_6225_);
                        crate::leanh::lean_dec(v___x_6236_);
                        if crate::leanh::lean_obj_tag(v___x_6237_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6237_, 1);
                            crate::leanh::lean_inc(v_a_6233_);
                            v___x_6238_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_6233_, v___x_6235_);
                            v___x_6239_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_6238_, v___x_6234_, v___y_6224_, v___y_6225_);
                            crate::leanh::lean_dec(v___x_6238_);
                            if crate::leanh::lean_obj_tag(v___x_6239_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6239_, 1);
                                v___x_6240_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_6233_, v___x_6235_);
                                v___x_6241_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_6240_, v___x_6234_, v___y_6224_, v___y_6225_);
                                crate::leanh::lean_dec(v___x_6240_);
                                if crate::leanh::lean_obj_tag(v___x_6241_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6241_, 1);
                                    v___x_6242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                    v___x_6243_ = 1usize;
                                    v___x_6244_ = lean_usize_add(v_i_6222_, v___x_6243_);
                                    v___x_6245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_6219_, v_as_6220_, v_sz_6221_, v___x_6244_, v___x_6242_, v___y_6224_, v___y_6225_);
                                    return v___x_6245_;
                                } else {
                                    v_a_6246_ = crate::leanh::lean_ctor_get(v___x_6241_, 0);
                                    v_isSharedCheck_6253_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6241_)) as u8;
                                    if v_isSharedCheck_6253_ == 0 {
                                        v___x_6248_ = v___x_6241_;
                                        v_isShared_6249_ = v_isSharedCheck_6253_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6246_);
                                        crate::leanh::lean_dec(v___x_6241_);
                                        v___x_6248_ = crate::leanh::lean_box(0);
                                        v_isShared_6249_ = v_isSharedCheck_6253_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6233_);
                                v_a_6254_ = crate::leanh::lean_ctor_get(v___x_6239_, 0);
                                v_isSharedCheck_6261_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6239_)) as u8;
                                if v_isSharedCheck_6261_ == 0 {
                                    v___x_6256_ = v___x_6239_;
                                    v_isShared_6257_ = v_isSharedCheck_6261_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6254_);
                                    crate::leanh::lean_dec(v___x_6239_);
                                    v___x_6256_ = crate::leanh::lean_box(0);
                                    v_isShared_6257_ = v_isSharedCheck_6261_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6233_);
                            v_a_6262_ = crate::leanh::lean_ctor_get(v___x_6237_, 0);
                            v_isSharedCheck_6269_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6237_)) as u8;
                            if v_isSharedCheck_6269_ == 0 {
                                v___x_6264_ = v___x_6237_;
                                v_isShared_6265_ = v_isSharedCheck_6269_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6262_);
                                crate::leanh::lean_dec(v___x_6237_);
                                v___x_6264_ = crate::leanh::lean_box(0);
                                v_isShared_6265_ = v_isSharedCheck_6269_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_6270_ = crate::leanh::lean_ctor_get(v___x_6232_, 0);
                        v_isSharedCheck_6282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6232_)) as u8;
                        if v_isSharedCheck_6282_ == 0 {
                            v___x_6272_ = v___x_6232_;
                            v_isShared_6273_ = v_isSharedCheck_6282_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6270_);
                            crate::leanh::lean_dec(v___x_6232_);
                            v___x_6272_ = crate::leanh::lean_box(0);
                            v_isShared_6273_ = v_isSharedCheck_6282_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6249_ == 0 {
                    v___x_6251_ = v___x_6248_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6252_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_a_6246_);
                    v___x_6251_ = v_reuseFailAlloc_6252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6251_;
            }
            3 => {
                if v_isShared_6257_ == 0 {
                    v___x_6259_ = v___x_6256_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6254_);
                    v___x_6259_ = v_reuseFailAlloc_6260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6259_;
            }
            5 => {
                if v_isShared_6265_ == 0 {
                    v___x_6267_ = v___x_6264_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6267_;
            }
            7 => {
                v_ref_6274_ = crate::leanh::lean_ctor_get(v___y_6224_, 7);
                v___x_6275_ = lean_io_error_to_string(v_a_6270_);
                v___x_6276_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                v___x_6277_ = l_Lean_MessageData_ofFormat(v___x_6276_);
                crate::leanh::lean_inc(v_ref_6274_);
                v___x_6278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6278_, 0, v_ref_6274_);
                crate::leanh::lean_ctor_set(v___x_6278_, 1, v___x_6277_);
                if v_isShared_6273_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6272_, 0, v___x_6278_);
                    v___x_6280_ = v___x_6272_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6281_, 0, v___x_6278_);
                    v___x_6280_ = v_reuseFailAlloc_6281_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___boxed(
    mut v___x_6283_: *mut crate::leanh::LeanObject,
    mut v_as_6284_: *mut crate::leanh::LeanObject,
    mut v_sz_6285_: *mut crate::leanh::LeanObject,
    mut v_i_6286_: *mut crate::leanh::LeanObject,
    mut v_b_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16788__boxed_6291_: u8 = 0;
    let mut v_sz_boxed_6292_: usize = 0;
    let mut v_i_boxed_6293_: usize = 0;
    let mut v_res_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16788__boxed_6291_ = (crate::leanh::lean_unbox(v___x_6283_) as u8);
    v_sz_boxed_6292_ = crate::leanh::lean_unbox_usize(v_sz_6285_);
    crate::leanh::lean_dec(v_sz_6285_);
    v_i_boxed_6293_ = crate::leanh::lean_unbox_usize(v_i_6286_);
    crate::leanh::lean_dec(v_i_6286_);
    v_res_6294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_16788__boxed_6291_, v_as_6284_, v_sz_boxed_6292_, v_i_boxed_6293_, v_b_6287_, v___y_6288_, v___y_6289_);
    crate::leanh::lean_dec(v___y_6289_);
    crate::leanh::lean_dec_ref(v___y_6288_);
    crate::leanh::lean_dec_ref(v_as_6284_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(
    mut v___x_6295_: u8,
    mut v_t_6296_: *mut crate::leanh::LeanObject,
    mut v_init_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v_a_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6315_: usize = 0;
    let mut v___x_6316_: usize = 0;
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6321_: u8 = 0;
    let mut v_fst_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v_a_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6335_: u8 = 0;
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6339_: u8 = 0;
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_a_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6344_: u8 = 0;
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6301_ = crate::leanh::lean_ctor_get(v_t_6296_, 0);
                v_tail_6302_ = crate::leanh::lean_ctor_get(v_t_6296_, 1);
                v___x_6303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6297_, v___x_6295_, v_root_6301_, v_init_6297_, v___y_6298_, v___y_6299_);
                if crate::leanh::lean_obj_tag(v___x_6303_) == 0 {
                    v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6340_ = (!crate::leanh::lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6340_ == 0 {
                        v___x_6306_ = v___x_6303_;
                        v_isShared_6307_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6304_);
                        crate::leanh::lean_dec(v___x_6303_);
                        v___x_6306_ = crate::leanh::lean_box(0);
                        v_isShared_6307_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6341_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6348_ = (!crate::leanh::lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6348_ == 0 {
                        v___x_6343_ = v___x_6303_;
                        v_isShared_6344_ = v_isSharedCheck_6348_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6341_);
                        crate::leanh::lean_dec(v___x_6303_);
                        v___x_6343_ = crate::leanh::lean_box(0);
                        v_isShared_6344_ = v_isSharedCheck_6348_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6304_) == 0 {
                    v_a_6308_ = crate::leanh::lean_ctor_get(v_a_6304_, 0);
                    crate::leanh::lean_inc(v_a_6308_);
                    crate::leanh::lean_dec_ref_known(v_a_6304_, 1);
                    if v_isShared_6307_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6306_, 0, v_a_6308_);
                        v___x_6310_ = v___x_6306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_a_6308_);
                        v___x_6310_ = v_reuseFailAlloc_6311_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6306_);
                    v_a_6312_ = crate::leanh::lean_ctor_get(v_a_6304_, 0);
                    crate::leanh::lean_inc(v_a_6312_);
                    crate::leanh::lean_dec_ref_known(v_a_6304_, 1);
                    v___x_6313_ = crate::leanh::lean_box(0);
                    v___x_6314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6314_, 0, v___x_6313_);
                    crate::leanh::lean_ctor_set(v___x_6314_, 1, v_a_6312_);
                    v_sz_6315_ = lean_array_size(v_tail_6302_);
                    v___x_6316_ = 0usize;
                    v___x_6317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_6295_, v_tail_6302_, v_sz_6315_, v___x_6316_, v___x_6314_, v___y_6298_, v___y_6299_);
                    if crate::leanh::lean_obj_tag(v___x_6317_) == 0 {
                        v_a_6318_ = crate::leanh::lean_ctor_get(v___x_6317_, 0);
                        v_isSharedCheck_6331_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6317_)) as u8;
                        if v_isSharedCheck_6331_ == 0 {
                            v___x_6320_ = v___x_6317_;
                            v_isShared_6321_ = v_isSharedCheck_6331_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6318_);
                            crate::leanh::lean_dec(v___x_6317_);
                            v___x_6320_ = crate::leanh::lean_box(0);
                            v_isShared_6321_ = v_isSharedCheck_6331_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6332_ = crate::leanh::lean_ctor_get(v___x_6317_, 0);
                        v_isSharedCheck_6339_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6317_)) as u8;
                        if v_isSharedCheck_6339_ == 0 {
                            v___x_6334_ = v___x_6317_;
                            v_isShared_6335_ = v_isSharedCheck_6339_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6332_);
                            crate::leanh::lean_dec(v___x_6317_);
                            v___x_6334_ = crate::leanh::lean_box(0);
                            v_isShared_6335_ = v_isSharedCheck_6339_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6310_;
            }
            3 => {
                v_fst_6322_ = crate::leanh::lean_ctor_get(v_a_6318_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6322_) == 0 {
                    v_snd_6323_ = crate::leanh::lean_ctor_get(v_a_6318_, 1);
                    crate::leanh::lean_inc(v_snd_6323_);
                    crate::leanh::lean_dec(v_a_6318_);
                    if v_isShared_6321_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6320_, 0, v_snd_6323_);
                        v___x_6325_ = v___x_6320_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_snd_6323_);
                        v___x_6325_ = v_reuseFailAlloc_6326_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6322_);
                    crate::leanh::lean_dec(v_a_6318_);
                    v_val_6327_ = crate::leanh::lean_ctor_get(v_fst_6322_, 0);
                    crate::leanh::lean_inc(v_val_6327_);
                    crate::leanh::lean_dec_ref_known(v_fst_6322_, 1);
                    if v_isShared_6321_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6320_, 0, v_val_6327_);
                        v___x_6329_ = v___x_6320_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_val_6327_);
                        v___x_6329_ = v_reuseFailAlloc_6330_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6325_;
            }
            5 => {
                return v___x_6329_;
            }
            6 => {
                if v_isShared_6335_ == 0 {
                    v___x_6337_ = v___x_6334_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_a_6332_);
                    v___x_6337_ = v_reuseFailAlloc_6338_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6337_;
            }
            8 => {
                if v_isShared_6344_ == 0 {
                    v___x_6346_ = v___x_6343_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_a_6341_);
                    v___x_6346_ = v_reuseFailAlloc_6347_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6___boxed(
    mut v___x_6349_: *mut crate::leanh::LeanObject,
    mut v_t_6350_: *mut crate::leanh::LeanObject,
    mut v_init_6351_: *mut crate::leanh::LeanObject,
    mut v___y_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_16912__boxed_6355_: u8 = 0;
    let mut v_res_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16912__boxed_6355_ = (crate::leanh::lean_unbox(v___x_6349_) as u8);
    v_res_6356_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(
            v___x_16912__boxed_6355_,
            v_t_6350_,
            v_init_6351_,
            v___y_6352_,
            v___y_6353_,
        );
    crate::leanh::lean_dec(v___y_6353_);
    crate::leanh::lean_dec_ref(v___y_6352_);
    crate::leanh::lean_dec_ref(v_t_6350_);
    return v_res_6356_;
}
pub unsafe fn l_Lean_Linter_List_listVariablesLinter___lam__0(
    mut v_stx_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v_v_6377_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6388_: u8 = 0;
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v_unused_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6361_ = lean_st_ref_get(v___y_6359_);
                v_scopes_6365_ = crate::leanh::lean_ctor_get(v___x_6361_, 2);
                crate::leanh::lean_inc(v_scopes_6365_);
                crate::leanh::lean_dec(v___x_6361_);
                v___x_6366_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_6367_ = l_List_head_x21___redArg(v___x_6366_, v_scopes_6365_);
                crate::leanh::lean_dec(v_scopes_6365_);
                v_opts_6368_ = crate::leanh::lean_ctor_get(v___x_6367_, 1);
                crate::leanh::lean_inc_ref(v_opts_6368_);
                crate::leanh::lean_dec(v___x_6367_);
                v___x_6369_ = l_Lean_Linter_List_linter_listVariables;
                v_name_6370_ = crate::leanh::lean_ctor_get(v___x_6369_, 0);
                v_map_6371_ = crate::leanh::lean_ctor_get(v_opts_6368_, 0);
                crate::leanh::lean_inc(v_map_6371_);
                crate::leanh::lean_dec_ref(v_opts_6368_);
                v___x_6372_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6371_, v_name_6370_);
                crate::leanh::lean_dec(v_map_6371_);
                if crate::leanh::lean_obj_tag(v___x_6372_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_6373_ = crate::leanh::lean_ctor_get(v___x_6372_, 0);
                    v_isSharedCheck_6405_ = (!crate::leanh::lean_is_exclusive(v___x_6372_)) as u8;
                    if v_isSharedCheck_6405_ == 0 {
                        v___x_6375_ = v___x_6372_;
                        v_isShared_6376_ = v_isSharedCheck_6405_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6373_);
                        crate::leanh::lean_dec(v___x_6372_);
                        v___x_6375_ = crate::leanh::lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6405_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6363_ = crate::leanh::lean_box(0);
                v___x_6364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6364_, 0, v___x_6363_);
                return v___x_6364_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_6373_) == 1 {
                    v_v_6377_ = crate::leanh::lean_ctor_get_uint8(v_val_6373_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_val_6373_, 0);
                    if v_v_6377_ == 0 {
                        crate::leanh::lean_del_object(v___x_6375_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6378_ = lean_st_ref_get(v___y_6359_);
                        v_messages_6379_ = crate::leanh::lean_ctor_get(v___x_6378_, 1);
                        crate::leanh::lean_inc_ref(v_messages_6379_);
                        crate::leanh::lean_dec(v___x_6378_);
                        v___x_6380_ = l_Lean_MessageLog_hasErrors(v_messages_6379_);
                        crate::leanh::lean_dec_ref(v_messages_6379_);
                        if v___x_6380_ == 0 {
                            v___x_6381_ = lean_st_ref_get(v___y_6359_);
                            v_infoState_6387_ = crate::leanh::lean_ctor_get(v___x_6381_, 8);
                            crate::leanh::lean_inc_ref(v_infoState_6387_);
                            crate::leanh::lean_dec(v___x_6381_);
                            v_enabled_6388_ = crate::leanh::lean_ctor_get_uint8(
                                v_infoState_6387_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            );
                            crate::leanh::lean_dec_ref(v_infoState_6387_);
                            if v_enabled_6388_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_6380_ == 0 {
                                    crate::leanh::lean_del_object(v___x_6375_);
                                    v___x_6389_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_6359_);
                                    v_a_6390_ = crate::leanh::lean_ctor_get(v___x_6389_, 0);
                                    crate::leanh::lean_inc(v_a_6390_);
                                    crate::leanh::lean_dec_ref(v___x_6389_);
                                    v___x_6391_ = crate::leanh::lean_box(0);
                                    v___x_6392_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_enabled_6388_, v_a_6390_, v___x_6391_, v___y_6358_, v___y_6359_);
                                    crate::leanh::lean_dec(v_a_6390_);
                                    if crate::leanh::lean_obj_tag(v___x_6392_) == 0 {
                                        v_isSharedCheck_6399_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6392_)) as u8;
                                        if v_isSharedCheck_6399_ == 0 {
                                            v_unused_6400_ =
                                                crate::leanh::lean_ctor_get(v___x_6392_, 0);
                                            crate::leanh::lean_dec(v_unused_6400_);
                                            v___x_6394_ = v___x_6392_;
                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_6392_);
                                            v___x_6394_ = crate::leanh::lean_box(0);
                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        return v___x_6392_;
                                    }
                                } else {
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_6401_ = crate::leanh::lean_box(0);
                            if v_isShared_6376_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6375_, 0);
                                crate::leanh::lean_ctor_set(v___x_6375_, 0, v___x_6401_);
                                v___x_6403_ = v___x_6375_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_6404_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6404_, 0, v___x_6401_);
                                v___x_6403_ = v_reuseFailAlloc_6404_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6375_);
                    crate::leanh::lean_dec(v_val_6373_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6383_ = crate::leanh::lean_box(0);
                if v_isShared_6376_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6375_, 0);
                    crate::leanh::lean_ctor_set(v___x_6375_, 0, v___x_6383_);
                    v___x_6385_ = v___x_6375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 0, v___x_6383_);
                    v___x_6385_ = v_reuseFailAlloc_6386_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6385_;
            }
            5 => {
                if v_isShared_6395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6394_, 0, v___x_6391_);
                    v___x_6397_ = v___x_6394_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6398_, 0, v___x_6391_);
                    v___x_6397_ = v_reuseFailAlloc_6398_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6397_;
            }
            7 => {
                return v___x_6403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_List_listVariablesLinter___lam__0___boxed(
    mut v_stx_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ =
        l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_6406_, v___y_6407_, v___y_6408_);
    crate::leanh::lean_dec(v___y_6408_);
    crate::leanh::lean_dec_ref(v___y_6407_);
    crate::leanh::lean_dec(v_stx_6406_);
    return v_res_6410_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(
    mut v_as_6424_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6425_: *mut crate::leanh::LeanObject,
    mut v_b_6426_: *mut crate::leanh::LeanObject,
    mut v_a_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6431_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(
            v_as_x27_6425_,
            v_b_6426_,
            v___y_6428_,
            v___y_6429_,
        );
    return v___x_6431_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___boxed(
    mut v_as_6432_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6433_: *mut crate::leanh::LeanObject,
    mut v_b_6434_: *mut crate::leanh::LeanObject,
    mut v_a_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6439_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(
        v_as_6432_,
        v_as_x27_6433_,
        v_b_6434_,
        v_a_6435_,
        v___y_6436_,
        v___y_6437_,
    );
    crate::leanh::lean_dec(v___y_6437_);
    crate::leanh::lean_dec_ref(v___y_6436_);
    crate::leanh::lean_dec(v_as_x27_6433_);
    crate::leanh::lean_dec(v_as_6432_);
    return v_res_6439_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(
    mut v_as_6440_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6441_: *mut crate::leanh::LeanObject,
    mut v_b_6442_: *mut crate::leanh::LeanObject,
    mut v_a_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6447_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(
            v_as_x27_6441_,
            v_b_6442_,
            v___y_6444_,
            v___y_6445_,
        );
    return v___x_6447_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___boxed(
    mut v_as_6448_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6449_: *mut crate::leanh::LeanObject,
    mut v_b_6450_: *mut crate::leanh::LeanObject,
    mut v_a_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6455_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(
        v_as_6448_,
        v_as_x27_6449_,
        v_b_6450_,
        v_a_6451_,
        v___y_6452_,
        v___y_6453_,
    );
    crate::leanh::lean_dec(v___y_6453_);
    crate::leanh::lean_dec_ref(v___y_6452_);
    crate::leanh::lean_dec(v_as_x27_6449_);
    crate::leanh::lean_dec(v_as_6448_);
    return v_res_6455_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(
    mut v_as_6456_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6457_: *mut crate::leanh::LeanObject,
    mut v_b_6458_: *mut crate::leanh::LeanObject,
    mut v_a_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
    mut v___y_6461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6463_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(
            v_as_x27_6457_,
            v_b_6458_,
            v___y_6460_,
            v___y_6461_,
        );
    return v___x_6463_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___boxed(
    mut v_as_6464_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6465_: *mut crate::leanh::LeanObject,
    mut v_b_6466_: *mut crate::leanh::LeanObject,
    mut v_a_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6471_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(
        v_as_6464_,
        v_as_x27_6465_,
        v_b_6466_,
        v_a_6467_,
        v___y_6468_,
        v___y_6469_,
    );
    crate::leanh::lean_dec(v___y_6469_);
    crate::leanh::lean_dec_ref(v___y_6468_);
    crate::leanh::lean_dec(v_as_x27_6465_);
    crate::leanh::lean_dec(v_as_6464_);
    return v_res_6471_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6473_ = l_Lean_Linter_List_listVariablesLinter;
    v___x_6474_ = l_Lean_Elab_Command_addLinter(v___x_6473_);
    return v___x_6474_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(
    mut v_a_6475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6476_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
    return v_res_6476_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_List(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
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
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_List_linter_indexVariables = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_List_linter_indexVariables);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_List_linter_listVariables = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_List_linter_listVariables);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_List(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_List(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
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
    res = runtime_initialize_Lean_Linter_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_List(builtin);
}
