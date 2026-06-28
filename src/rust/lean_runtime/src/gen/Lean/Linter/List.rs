// Lean compiler output
// Module: Lean.Linter.List
// Imports: Lean.Linter.Basic Lean.Server.InfoUtils Lean.Linter.Init
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 100, 101, 120, 86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,2370590245460535436 as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<106> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [86, 97, 108, 105, 100, 97, 116, 101, 32, 116, 104, 97, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 40, 101, 46, 103, 46, 32, 105, 110, 32, 96, 120, 115, 91, 105, 93, 96, 32, 111, 114, 32, 96, 120, 115, 46, 116, 97, 107, 101, 32, 105, 96, 41, 32, 97, 114, 101, 32, 111, 110, 108, 121, 32, 96, 105, 96, 44, 32, 96, 106, 96, 44, 32, 111, 114, 32, 96, 107, 96, 46, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,13480916849937425914 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9252344385775686671 as *mut LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,12101741544773259677 as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 115, 116, 86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject,4853507067084237010 as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [86, 97, 108, 105, 100, 97, 116, 101, 32, 116, 104, 97, 116, 32, 97, 108, 108, 32, 96, 76, 105, 115, 116, 96, 47, 96, 65, 114, 114, 97, 121, 96, 47, 96, 86, 101, 99, 116, 111, 114, 96, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 117, 115, 101, 32, 97, 108, 108, 111, 119, 101, 100, 32, 110, 97, 109, 101, 115, 46, 0]};
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,13480916849937425914 as *mut LeanObject] };
static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9252344385775686671 as *mut LeanObject] };
pub static l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__0_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject,12089079435222617387 as *mut LeanObject] };
static mut l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
                as *mut LeanObject,
            8467293704094663304 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
                as *mut LeanObject,
            10802932081047211230 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
                as *mut LeanObject,
            3872834428859331858 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
                as *mut LeanObject,
            2233317244024471518 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
                as *mut LeanObject,
            5193315113790084929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__11_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
                as *mut LeanObject,
            16034137926423127740 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
                as *mut LeanObject,
            1396115026687347110 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__14_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
                as *mut LeanObject,
            10539643452699375210 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__15_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
                as *mut LeanObject,
            16221596318437611981 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__2_value)
                as *mut LeanObject,
            18152428103632701704 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__18_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__4_value)
                as *mut LeanObject,
            9925259263419088478 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__19_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__6_value)
                as *mut LeanObject,
            6571270745476678546 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__20_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__8_value)
                as *mut LeanObject,
            16343519309823643998 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__21_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__10_value)
                as *mut LeanObject,
            12014922020157731009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
                as *mut LeanObject,
            5052701508307584446 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__25_value)
                as *mut LeanObject,
            4405791127581099400 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__26_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
                as *mut LeanObject,
            18119106984202331506 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
                as *mut LeanObject,
            10432512871714827331 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            105, 110, 115, 101, 114, 116, 73, 100, 120, 73, 102, 73, 110, 66, 111, 117, 110, 100,
            115, 0,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__30_value)
                as *mut LeanObject,
            737450741554540126 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
                as *mut LeanObject,
            14350272335116742732 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
                as *mut LeanObject,
            8050958516035322399 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__35_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__23_value)
                as *mut LeanObject,
            4957202763588502154 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
                as *mut LeanObject,
            3630988818933640571 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
                as *mut LeanObject,
            6372375211616468373 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__40_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__28_value)
                as *mut LeanObject,
            658061322716625603 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__41_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__13_value)
                as *mut LeanObject,
            3883600285600967666 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__42_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__32_value)
                as *mut LeanObject,
            4767221380455929548 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__43_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__34_value)
                as *mut LeanObject,
            4628900765690287007 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
                as *mut LeanObject,
            2036269554361060417 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__46_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
                as *mut LeanObject,
            1024280003738481991 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__47_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__48_value)
                as *mut LeanObject,
            17673153628822191198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__49_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
                as *mut LeanObject,
            3144473122610617097 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__50_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__45_value)
                as *mut LeanObject,
            16801329853220961729 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__51_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__37_value)
                as *mut LeanObject,
            15138447177923935175 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__52_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__39_value)
                as *mut LeanObject,
            16742334573394357385 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__54_value)
                as *mut LeanObject,
            1284173141442213452 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__55_value)
                as *mut LeanObject,
            14790288273250445109 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__56_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__57_value)
                as *mut LeanObject,
            854136310249810287 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__58_value)
                as *mut LeanObject,
            8801718159307809986 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___lam__2___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__59_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_numericalIndices___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_numericalIndices___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_numericalIndices___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_numericalIndices___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_numericalIndices___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_List_numericalIndices___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalIndices___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
                as *mut LeanObject,
            17402736243434278163 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__1_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
                as *mut LeanObject,
            10154756713319201683 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__2_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__0_value)
                as *mut LeanObject,
            7114987585215218527 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
                as *mut LeanObject,
            7934366685309624176 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
                as *mut LeanObject,
            10856004936568328432 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__7_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__5_value)
                as *mut LeanObject,
            3800766237690652964 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__17_value)
                as *mut LeanObject,
            2228683986675333841 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
                as *mut LeanObject,
            15402697716333298155 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value)
                as *mut LeanObject,
            8749134177695247953 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
                as *mut LeanObject,
            2966064990585596011 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__11_value)
        as *mut LeanObject;
static l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__9_value)
                as *mut LeanObject,
            634820988191375095 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___lam__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_numericalWidths___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_numericalWidths___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_numericalWidths___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_List_numericalWidths___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_numericalWidths___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_numericalWidths___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_bitVecWidths___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__0_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_bitVecWidths___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_bitVecWidths___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_bitVecWidths___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_bitVecWidths___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_bitVecWidths___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 129, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0_value) as *mut LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 130, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0_value) as *mut LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 131, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0_value) as *mut LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 130, 132, 0]};
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0_value) as *mut LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_List_allowedIndices___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__5_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedIndices___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__5_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__6_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__7_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__8_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__9_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__10_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedIndices___closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedIndices___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedIndices: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__11_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedWidths___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedWidths___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedWidths___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedWidths___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__3_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedWidths___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedWidths___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__5_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedIndices___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedWidths___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__6_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedWidths___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__7_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedWidths___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_allowedWidths___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedWidths: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__8_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedBitVecWidths___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedBitVecWidths___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_allowedBitVecWidths___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedBitVecWidths___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedBitVecWidths: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedBitVecWidths___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 119, 105, 100, 116, 104, 58, 32, 117, 115, 101, 32, 96, 110, 96, 32, 111, 114, 32, 96, 109, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 66, 105, 116, 86, 101, 99, 32, 119, 105, 100, 116, 104, 58, 32, 117, 115, 101, 32, 96, 119, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value: LeanStringObject<65> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 58, 32, 117, 115, 101, 32, 96, 105, 96, 44, 32, 96, 106, 96, 44, 32, 111, 114, 32, 96, 107, 96, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_indexLinter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_indexLinter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_indexLinter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_indexLinter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__2_value) as *mut LeanObject;
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_List_indexLinter___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,13480916849937425914 as *mut LeanObject] };
pub static l_Lean_Linter_List_indexLinter___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__2_value) as *mut LeanObject,
        6834480939803322061 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_indexLinter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter_List_indexLinter___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_List_indexLinter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_indexLinter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_indexLinter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__3_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__5_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__5_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__6_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__6_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__7_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__7_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__8_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__8_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__9_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__10_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__11_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__11_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__12_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_allowedListNames___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__12_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__12_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__13_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__14_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__14_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__15_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__16_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__16_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__17_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__18_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__18_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__19_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__20_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__21_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__22_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__22_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__23_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__23_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__24_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__24_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__25_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__25_value) as *mut LeanObject;
pub static l_Lean_Linter_List_allowedListNames___closed__26_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_allowedWidths___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__25_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_allowedListNames___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__26_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedListNames: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__26_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedArrayNames: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value) as *mut LeanObject;
pub static mut l_Lean_Linter_List_allowedVectorNames: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_allowedListNames___closed__21_value) as *mut LeanObject;
pub static l_Lean_Linter_List_binders___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_List_binders___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_List_binders___lam__0___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__0_value)
                as *mut LeanObject,
            9833841078580172006 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_binders___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_binders___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Linter_List_binders___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_List_binders___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 65, 114, 114, 97, 121, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 115, 115, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_List_numericalIndices___lam__2___closed__1_value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 76, 105, 115, 116, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [76, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [70, 111, 114, 98, 105, 100, 100, 101, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 97, 115, 32, 97, 32, 96, 86, 101, 99, 116, 111, 114, 96, 32, 110, 97, 109, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_List_listVariablesLinter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_List_listVariablesLinter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_List_listVariablesLinter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_listVariablesLinter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            108, 105, 115, 116, 86, 97, 114, 105, 97, 98, 108, 101, 115, 76, 105, 110, 116, 101,
            114, 0,
        ],
    };
static mut l_Lean_Linter_List_listVariablesLinter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__2_value)
        as *mut LeanObject;
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__5_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__6_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__7_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__value) as *mut LeanObject,13480916849937425914 as *mut LeanObject] };
pub static l_Lean_Linter_List_listVariablesLinter___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__2_value)
                as *mut LeanObject,
            14015206877912852658 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_listVariablesLinter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Linter_List_listVariablesLinter___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_List_listVariablesLinter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_List_listVariablesLinter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_List_listVariablesLinter___closed__4_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(
    mut v_name_3239_: *mut LeanObject,
    mut v_decl_3240_: *mut LeanObject,
    mut v_ref_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_unused_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3243_ = lean_ctor_get(v_decl_3240_, 0);
                v_descr_3244_ = lean_ctor_get(v_decl_3240_, 1);
                v_deprecation_x3f_3245_ = lean_ctor_get(v_decl_3240_, 2);
                v___x_3246_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3247_ = (lean_unbox(v_defValue_3243_) as u8);
                lean_ctor_set_uint8(v___x_3246_, 0 as u32, v___x_3247_);
                lean_inc(v_deprecation_x3f_3245_);
                lean_inc_ref(v_descr_3244_);
                lean_inc_n(v_name_3239_, 2);
                v___x_3248_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3248_, 0, v_name_3239_);
                lean_ctor_set(v___x_3248_, 1, v_ref_3241_);
                lean_ctor_set(v___x_3248_, 2, v___x_3246_);
                lean_ctor_set(v___x_3248_, 3, v_descr_3244_);
                lean_ctor_set(v___x_3248_, 4, v_deprecation_x3f_3245_);
                v___x_3249_ = lean_register_option(v_name_3239_, v___x_3248_);
                if lean_obj_tag(v___x_3249_) == 0 {
                    v_isSharedCheck_3257_ = (!lean_is_exclusive(v___x_3249_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v_unused_3258_ = lean_ctor_get(v___x_3249_, 0);
                        lean_dec(v_unused_3258_);
                        v___x_3251_ = v___x_3249_;
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3249_);
                        v___x_3251_ = lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3239_);
                    v_a_3259_ = lean_ctor_get(v___x_3249_, 0);
                    v_isSharedCheck_3266_ = (!lean_is_exclusive(v___x_3249_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3261_ = v___x_3249_;
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3259_);
                        lean_dec(v___x_3249_);
                        v___x_3261_ = lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_3243_);
                v___x_3253_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3253_, 0, v_name_3239_);
                lean_ctor_set(v___x_3253_, 1, v_defValue_3243_);
                if v_isShared_3252_ == 0 {
                    lean_ctor_set(v___x_3251_, 0, v___x_3253_);
                    v___x_3255_ = v___x_3251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
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
                    v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
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
    mut v_name_3267_: *mut LeanObject,
    mut v_decl_3268_: *mut LeanObject,
    mut v_ref_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3271_: *mut LeanObject = core::ptr::null_mut();
    v_res_3271_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v_name_3267_, v_decl_3268_, v_ref_3269_);
    lean_dec_ref(v_decl_3268_);
    return v_res_3271_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3293_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__2_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3294_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3295_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__8_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_;
    v___x_3296_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_3293_, v___x_3294_, v___x_3295_);
    return v___x_3296_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4____boxed(
    mut v_a_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3298_: *mut LeanObject = core::ptr::null_mut();
    v_res_3298_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
    return v_res_3298_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    v___x_3316_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__1_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3317_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__3_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3318_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn___closed__4_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_;
    v___x_3319_ = l_Lean_Option_register___at___00__private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4__spec__0(v___x_3316_, v___x_3317_, v___x_3318_);
    return v___x_3319_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4____boxed(
    mut v_a_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3321_: *mut LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
    return v_res_3321_;
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__0(
    mut v_i_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ = lean_box(0);
    v___x_3324_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3324_, 0, v_i_3322_);
    lean_ctor_set(v___x_3324_, 1, v___x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Lean_Linter_List_numericalIndices___lam__1(
    mut v_i_3325_: *mut LeanObject,
    mut v_j_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    v___x_3327_ = lean_box(0);
    v___x_3328_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3328_, 0, v_j_3326_);
    lean_ctor_set(v___x_3328_, 1, v___x_3327_);
    v___x_3329_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3329_, 0, v_i_3325_);
    lean_ctor_set(v___x_3329_, 1, v___x_3328_);
    return v___x_3329_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
    mut v_i_3330_: *mut LeanObject,
    mut v_stx_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v_fvarId_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3332_) == 0 {
                    lean_dec(v_stx_3331_);
                    lean_dec_ref(v_i_3330_);
                    v___x_3334_ = lean_array_to_list(v_a_3333_);
                    return v___x_3334_;
                } else {
                    v_head_3335_ = lean_ctor_get(v_a_3332_, 0);
                    if lean_obj_tag(v_head_3335_) == 1 {
                        lean_inc_ref(v_head_3335_);
                        v_tail_3336_ = lean_ctor_get(v_a_3332_, 1);
                        v_isSharedCheck_3351_ = (!lean_is_exclusive(v_a_3332_)) as u8;
                        if v_isSharedCheck_3351_ == 0 {
                            v_unused_3352_ = lean_ctor_get(v_a_3332_, 0);
                            lean_dec(v_unused_3352_);
                            v___x_3338_ = v_a_3332_;
                            v_isShared_3339_ = v_isSharedCheck_3351_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_3336_);
                            lean_dec(v_a_3332_);
                            v___x_3338_ = lean_box(0);
                            v_isShared_3339_ = v_isSharedCheck_3351_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_3353_ = lean_ctor_get(v_a_3332_, 1);
                        lean_inc(v_tail_3353_);
                        lean_dec_ref_known(v_a_3332_, 2);
                        v_a_3332_ = v_tail_3353_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_3340_ = lean_ctor_get(v_head_3335_, 0);
                lean_inc(v_fvarId_3340_);
                lean_dec_ref_known(v_head_3335_, 1);
                v_lctx_3341_ = lean_ctor_get(v_i_3330_, 1);
                lean_inc_ref(v_lctx_3341_);
                v___x_3342_ = lean_local_ctx_find(v_lctx_3341_, v_fvarId_3340_);
                if lean_obj_tag(v___x_3342_) == 0 {
                    lean_del_object(v___x_3338_);
                    v_a_3332_ = v_tail_3336_;
                    state = 0;
                    continue;
                } else {
                    v_val_3344_ = lean_ctor_get(v___x_3342_, 0);
                    lean_inc(v_val_3344_);
                    lean_dec_ref_known(v___x_3342_, 1);
                    v___x_3345_ = l_Lean_LocalDecl_userName(v_val_3344_);
                    lean_dec(v_val_3344_);
                    lean_inc(v_stx_3331_);
                    if v_isShared_3339_ == 0 {
                        lean_ctor_set_tag(v___x_3338_, 0);
                        lean_ctor_set(v___x_3338_, 1, v___x_3345_);
                        lean_ctor_set(v___x_3338_, 0, v_stx_3331_);
                        v___x_3347_ = v___x_3338_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_stx_3331_);
                        lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3345_);
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
    mut v___f_3490_: *mut LeanObject,
    mut v___f_3491_: *mut LeanObject,
    mut v_x_3492_: *mut LeanObject,
    mut v_info_3493_: *mut LeanObject,
    mut v_x_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v___y_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: u8 = 0;
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_unused_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_3493_) == 1 {
                    v_i_3495_ = lean_ctor_get(v_info_3493_, 0);
                    lean_inc_ref(v_i_3495_);
                    v_expr_3496_ = lean_ctor_get(v_i_3495_, 3);
                    lean_inc_ref(v_expr_3496_);
                    v___x_3497_ = l_Lean_Expr_cleanupAnnotations(v_expr_3496_);
                    v___x_3498_ = l_Lean_Expr_isApp(v___x_3497_);
                    if v___x_3498_ == 0 {
                        lean_dec_ref(v___x_3497_);
                        lean_dec_ref_known(v_info_3493_, 1);
                        lean_dec_ref(v_i_3495_);
                        lean_dec_ref(v___f_3491_);
                        lean_dec_ref(v___f_3490_);
                        v___x_3499_ = lean_box(0);
                        return v___x_3499_;
                    } else {
                        v_arg_3500_ = lean_ctor_get(v___x_3497_, 1);
                        lean_inc_ref(v_arg_3500_);
                        v___x_3501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3497_);
                        v___x_3502_ = l_Lean_Expr_isApp(v___x_3501_);
                        if v___x_3502_ == 0 {
                            lean_dec_ref(v___x_3501_);
                            lean_dec_ref(v_arg_3500_);
                            lean_dec_ref_known(v_info_3493_, 1);
                            lean_dec_ref(v_i_3495_);
                            lean_dec_ref(v___f_3491_);
                            lean_dec_ref(v___f_3490_);
                            v___x_3503_ = lean_box(0);
                            return v___x_3503_;
                        } else {
                            v_arg_3504_ = lean_ctor_get(v___x_3501_, 1);
                            lean_inc_ref(v_arg_3504_);
                            v___x_3505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3501_);
                            v___x_3506_ = l_Lean_Expr_isApp(v___x_3505_);
                            if v___x_3506_ == 0 {
                                lean_dec_ref(v___x_3505_);
                                lean_dec_ref(v_arg_3504_);
                                lean_dec_ref(v_arg_3500_);
                                lean_dec_ref_known(v_info_3493_, 1);
                                lean_dec_ref(v_i_3495_);
                                lean_dec_ref(v___f_3491_);
                                lean_dec_ref(v___f_3490_);
                                v___x_3507_ = lean_box(0);
                                return v___x_3507_;
                            } else {
                                v_arg_3508_ = lean_ctor_get(v___x_3505_, 1);
                                lean_inc_ref(v_arg_3508_);
                                v_stx_3509_ = l_Lean_Elab_Info_stx(v_info_3493_);
                                v_isSharedCheck_3649_ = (!lean_is_exclusive(v_info_3493_)) as u8;
                                if v_isSharedCheck_3649_ == 0 {
                                    v_unused_3650_ = lean_ctor_get(v_info_3493_, 0);
                                    lean_dec(v_unused_3650_);
                                    v___x_3511_ = v_info_3493_;
                                    v_isShared_3512_ = v_isSharedCheck_3649_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_info_3493_);
                                    v___x_3511_ = lean_box(0);
                                    v_isShared_3512_ = v_isSharedCheck_3649_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_info_3493_);
                    lean_dec_ref(v___f_3491_);
                    lean_dec_ref(v___f_3490_);
                    v___x_3651_ = lean_box(0);
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
                                                        lean_dec_ref(v___x_3521_);
                                                        lean_del_object(v___x_3511_);
                                                        lean_dec(v_stx_3509_);
                                                        lean_dec_ref(v_arg_3508_);
                                                        lean_dec_ref(v_arg_3504_);
                                                        lean_dec_ref(v_arg_3500_);
                                                        lean_dec_ref(v_i_3495_);
                                                        lean_dec_ref(v___f_3491_);
                                                        lean_dec_ref(v___f_3490_);
                                                        v___x_3541_ = lean_box(0);
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
lean_dec_ref(v___x_3542_);
lean_del_object(v___x_3511_);
lean_dec(v_stx_3509_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v_i_3495_);
lean_dec_ref(v___f_3491_);
lean_dec_ref(v___f_3490_);
v___x_3574_ = lean_box(0);
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
lean_dec_ref(v___x_3575_);
lean_del_object(v___x_3511_);
lean_dec(v_stx_3509_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v_i_3495_);
lean_dec_ref(v___f_3491_);
lean_dec_ref(v___f_3490_);
v___x_3593_ = lean_box(0);
return v___x_3593_;
} else {
v___x_3594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3575_);
v___x_3595_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__51;
v___x_3596_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3595_);
if v___x_3596_ == 0 {
lean_dec_ref(v___f_3491_);
v___x_3597_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__52;
v___x_3598_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3597_);
if v___x_3598_ == 0 {
v___x_3599_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__53;
v___x_3600_ = l_Lean_Expr_isConstOf(v___x_3594_, v___x_3599_);
if v___x_3600_ == 0 {
lean_dec_ref(v_arg_3508_);
v___x_3601_ = l_Lean_Expr_isApp(v___x_3594_);
if v___x_3601_ == 0 {
lean_dec_ref(v___x_3594_);
lean_del_object(v___x_3511_);
lean_dec(v_stx_3509_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v_i_3495_);
lean_dec_ref(v___f_3490_);
v___x_3602_ = lean_box(0);
return v___x_3602_;
} else {
v___x_3603_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3594_);
v___x_3604_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__56;
v___x_3605_ = l_Lean_Expr_isConstOf(v___x_3603_, v___x_3604_);
if v___x_3605_ == 0 {
lean_dec_ref(v_arg_3500_);
v___x_3606_ = l_Lean_Expr_isApp(v___x_3603_);
if v___x_3606_ == 0 {
lean_dec_ref(v___x_3603_);
lean_del_object(v___x_3511_);
lean_dec(v_stx_3509_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_i_3495_);
lean_dec_ref(v___f_3490_);
v___x_3607_ = lean_box(0);
return v___x_3607_;
} else {
v___x_3608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3603_);
v___x_3609_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__59;
v___x_3610_ = l_Lean_Expr_isConstOf(v___x_3608_, v___x_3609_);
lean_dec_ref(v___x_3608_);
if v___x_3610_ == 0 {
lean_del_object(v___x_3511_);
lean_dec(v_stx_3509_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_i_3495_);
lean_dec_ref(v___f_3490_);
v___x_3611_ = lean_box(0);
return v___x_3611_;
} else {
v___x_3612_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3612_;
state = 2; continue;
}
}
} else {
lean_dec_ref(v___x_3603_);
lean_dec_ref(v_arg_3504_);
v___x_3613_ = lean_apply_1(v___f_3490_, v_arg_3500_);
v___y_3514_ = v___x_3613_;
state = 2; continue;
}
}
} else {
lean_dec_ref(v___x_3594_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
v___x_3614_ = lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3614_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3594_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
v___x_3615_ = lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3615_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3594_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3490_);
v___x_3616_ = lean_apply_2(v___f_3491_, v_arg_3508_, v_arg_3504_);
v___y_3514_ = v___x_3616_;
state = 2; continue;
}
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3617_ = lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3617_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3618_ = lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3618_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3619_ = lean_apply_1(v___f_3490_, v_arg_3508_);
v___y_3514_ = v___x_3619_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3490_);
v___x_3620_ = lean_apply_2(v___f_3491_, v_arg_3508_, v_arg_3504_);
v___y_3514_ = v___x_3620_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v___f_3490_);
v___x_3621_ = lean_apply_2(v___f_3491_, v_arg_3504_, v_arg_3500_);
v___y_3514_ = v___x_3621_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3622_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3622_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3623_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3623_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3624_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3624_;
state = 2; continue;
}
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3625_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3625_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3626_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3626_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3627_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3627_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v___f_3490_);
v___x_3628_ = lean_apply_2(v___f_3491_, v_arg_3504_, v_arg_3500_);
v___y_3514_ = v___x_3628_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3629_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3629_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3630_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3630_;
state = 2; continue;
}
} else {
lean_dec_ref(v___x_3542_);
lean_dec_ref(v_arg_3508_);
lean_dec_ref(v_arg_3500_);
lean_dec_ref(v___f_3491_);
v___x_3631_ = lean_apply_1(v___f_3490_, v_arg_3504_);
v___y_3514_ = v___x_3631_;
state = 2; continue;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v___x_3542_);
                                                                                        lean_dec_ref(v_arg_3508_);
                                                                                        lean_dec_ref(v_arg_3500_);
                                                                                        lean_dec_ref(v___f_3491_);
                                                                                        v___x_3632_ = lean_apply_1(v___f_3490_, v_arg_3504_);
                                                                                        v___y_3514_ = v___x_3632_;
                                                                                        state = 2;
                                                                                        continue;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v___x_3542_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_3508_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_3500_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v___f_3491_,
                                                                                    );
                                                                                    v___x_3633_ = lean_apply_1(v___f_3490_, v_arg_3504_);
                                                                                    v___y_3514_ =
                                                                                        v___x_3633_;
                                                                                    state = 2;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v___x_3542_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3508_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_3500_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v___f_3491_,
                                                                                );
                                                                                v___x_3634_ =
                                                                                    lean_apply_1(
                                                                                        v___f_3490_,
                                                                                        v_arg_3504_,
                                                                                    );
                                                                                v___y_3514_ =
                                                                                    v___x_3634_;
                                                                                state = 2;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v___x_3542_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3508_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_3504_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v___f_3491_,
                                                                            );
                                                                            v___x_3635_ =
                                                                                lean_apply_1(
                                                                                    v___f_3490_,
                                                                                    v_arg_3500_,
                                                                                );
                                                                            v___y_3514_ =
                                                                                v___x_3635_;
                                                                            state = 2;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_3542_);
                                                                        lean_dec_ref(v_arg_3508_);
                                                                        lean_dec_ref(v_arg_3504_);
                                                                        lean_dec_ref(v___f_3491_);
                                                                        v___x_3636_ = lean_apply_1(
                                                                            v___f_3490_,
                                                                            v_arg_3500_,
                                                                        );
                                                                        v___y_3514_ = v___x_3636_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_3542_);
                                                                    lean_dec_ref(v_arg_3508_);
                                                                    lean_dec_ref(v_arg_3504_);
                                                                    lean_dec_ref(v___f_3491_);
                                                                    v___x_3637_ = lean_apply_1(
                                                                        v___f_3490_,
                                                                        v_arg_3500_,
                                                                    );
                                                                    v___y_3514_ = v___x_3637_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_3542_);
                                                                lean_dec_ref(v_arg_3508_);
                                                                lean_dec_ref(v_arg_3504_);
                                                                lean_dec_ref(v___f_3491_);
                                                                v___x_3638_ = lean_apply_1(
                                                                    v___f_3490_,
                                                                    v_arg_3500_,
                                                                );
                                                                v___y_3514_ = v___x_3638_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_3542_);
                                                            lean_dec_ref(v_arg_3508_);
                                                            lean_dec_ref(v_arg_3504_);
                                                            lean_dec_ref(v___f_3491_);
                                                            v___x_3639_ = lean_apply_1(
                                                                v___f_3490_,
                                                                v_arg_3500_,
                                                            );
                                                            v___y_3514_ = v___x_3639_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_3521_);
                                                    lean_dec_ref(v_arg_3508_);
                                                    lean_dec_ref(v_arg_3500_);
                                                    lean_dec_ref(v___f_3491_);
                                                    v___x_3640_ =
                                                        lean_apply_1(v___f_3490_, v_arg_3504_);
                                                    v___y_3514_ = v___x_3640_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v___x_3521_);
                                                lean_dec_ref(v_arg_3508_);
                                                lean_dec_ref(v_arg_3500_);
                                                lean_dec_ref(v___f_3491_);
                                                v___x_3641_ =
                                                    lean_apply_1(v___f_3490_, v_arg_3504_);
                                                v___y_3514_ = v___x_3641_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3521_);
                                            lean_dec_ref(v_arg_3508_);
                                            lean_dec_ref(v_arg_3504_);
                                            lean_dec_ref(v___f_3491_);
                                            v___x_3642_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                                            v___y_3514_ = v___x_3642_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3521_);
                                        lean_dec_ref(v_arg_3508_);
                                        lean_dec_ref(v_arg_3504_);
                                        lean_dec_ref(v___f_3491_);
                                        v___x_3643_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                                        v___y_3514_ = v___x_3643_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_3521_);
                                    lean_dec_ref(v_arg_3508_);
                                    lean_dec_ref(v_arg_3504_);
                                    lean_dec_ref(v___f_3491_);
                                    v___x_3644_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                                    v___y_3514_ = v___x_3644_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_3521_);
                                lean_dec_ref(v_arg_3508_);
                                lean_dec_ref(v_arg_3504_);
                                lean_dec_ref(v___f_3491_);
                                v___x_3645_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                                v___y_3514_ = v___x_3645_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_3521_);
                            lean_dec_ref(v_arg_3508_);
                            lean_dec_ref(v_arg_3504_);
                            lean_dec_ref(v___f_3491_);
                            v___x_3646_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                            v___y_3514_ = v___x_3646_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3521_);
                        lean_dec_ref(v_arg_3508_);
                        lean_dec_ref(v_arg_3504_);
                        lean_dec_ref(v___f_3491_);
                        v___x_3647_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                        v___y_3514_ = v___x_3647_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3521_);
                    lean_dec_ref(v_arg_3508_);
                    lean_dec_ref(v_arg_3504_);
                    lean_dec_ref(v___f_3491_);
                    v___x_3648_ = lean_apply_1(v___f_3490_, v_arg_3500_);
                    v___y_3514_ = v___x_3648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v___y_3514_) == 0 {
                    lean_del_object(v___x_3511_);
                    lean_dec(v_stx_3509_);
                    lean_dec_ref(v_i_3495_);
                    v___x_3515_ = lean_box(0);
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
                        lean_ctor_set(v___x_3511_, 0, v___x_3517_);
                        v___x_3519_ = v___x_3511_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
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
    mut v___f_3652_: *mut LeanObject,
    mut v___f_3653_: *mut LeanObject,
    mut v_x_3654_: *mut LeanObject,
    mut v_info_3655_: *mut LeanObject,
    mut v_x_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3657_: *mut LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_Linter_List_numericalIndices___lam__2(
        v___f_3652_,
        v___f_3653_,
        v_x_3654_,
        v_info_3655_,
        v_x_3656_,
    );
    lean_dec_ref(v_x_3656_);
    lean_dec_ref(v_x_3654_);
    return v_res_3657_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(
    mut v_a_3658_: *mut LeanObject,
    mut v_a_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3658_) == 0 {
                    v___x_3660_ = lean_array_to_list(v_a_3659_);
                    return v___x_3660_;
                } else {
                    v_head_3661_ = lean_ctor_get(v_a_3658_, 0);
                    lean_inc(v_head_3661_);
                    v_tail_3662_ = lean_ctor_get(v_a_3658_, 1);
                    lean_inc(v_tail_3662_);
                    lean_dec_ref_known(v_a_3658_, 2);
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
    mut v_t_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    v___f_3671_ = l_Lean_Linter_List_numericalIndices___closed__2;
    v___x_3672_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3671_, v_t_3670_);
    v___x_3673_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3674_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3672_, v___x_3673_);
    return v___x_3674_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths___lam__0(
    mut v_n_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ = lean_box(0);
    v___x_3677_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3677_, 0, v_n_3675_);
    lean_ctor_set(v___x_3677_, 1, v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths___lam__1(
    mut v___f_3710_: *mut LeanObject,
    mut v_x_3711_: *mut LeanObject,
    mut v_info_3712_: *mut LeanObject,
    mut v_x_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___y_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_unused_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_3712_) == 1 {
                    v_i_3714_ = lean_ctor_get(v_info_3712_, 0);
                    lean_inc_ref(v_i_3714_);
                    v_expr_3715_ = lean_ctor_get(v_i_3714_, 3);
                    lean_inc_ref(v_expr_3715_);
                    v___x_3716_ = l_Lean_Expr_cleanupAnnotations(v_expr_3715_);
                    v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
                    if v___x_3717_ == 0 {
                        lean_dec_ref(v___x_3716_);
                        lean_dec_ref(v_i_3714_);
                        lean_dec_ref_known(v_info_3712_, 1);
                        lean_dec_ref(v___f_3710_);
                        v___x_3718_ = lean_box(0);
                        return v___x_3718_;
                    } else {
                        v_arg_3719_ = lean_ctor_get(v___x_3716_, 1);
                        lean_inc_ref(v_arg_3719_);
                        v_stx_3720_ = l_Lean_Elab_Info_stx(v_info_3712_);
                        v_isSharedCheck_3771_ = (!lean_is_exclusive(v_info_3712_)) as u8;
                        if v_isSharedCheck_3771_ == 0 {
                            v_unused_3772_ = lean_ctor_get(v_info_3712_, 0);
                            lean_dec(v_unused_3772_);
                            v___x_3722_ = v_info_3712_;
                            v_isShared_3723_ = v_isSharedCheck_3771_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_info_3712_);
                            v___x_3722_ = lean_box(0);
                            v_isShared_3723_ = v_isSharedCheck_3771_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_info_3712_);
                    lean_dec_ref(v___f_3710_);
                    v___x_3773_ = lean_box(0);
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
                                lean_dec_ref(v___x_3732_);
                                lean_del_object(v___x_3722_);
                                lean_dec(v_stx_3720_);
                                lean_dec_ref(v_arg_3719_);
                                lean_dec_ref(v_i_3714_);
                                lean_dec_ref(v___f_3710_);
                                v___x_3740_ = lean_box(0);
                                return v___x_3740_;
                            } else {
                                v_arg_3741_ = lean_ctor_get(v___x_3732_, 1);
                                lean_inc_ref(v_arg_3741_);
                                v___x_3742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3732_);
                                v___x_3743_ =
                                    l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                                v___x_3744_ = l_Lean_Expr_isConstOf(v___x_3742_, v___x_3743_);
                                if v___x_3744_ == 0 {
                                    lean_dec_ref(v_arg_3719_);
                                    v___x_3745_ = l_Lean_Expr_isApp(v___x_3742_);
                                    if v___x_3745_ == 0 {
                                        lean_dec_ref(v___x_3742_);
                                        lean_dec_ref(v_arg_3741_);
                                        lean_del_object(v___x_3722_);
                                        lean_dec(v_stx_3720_);
                                        lean_dec_ref(v_i_3714_);
                                        lean_dec_ref(v___f_3710_);
                                        v___x_3746_ = lean_box(0);
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
                                                            lean_dec_ref(v___x_3747_);
                                                            if v___x_3759_ == 0 {
                                                                lean_dec_ref(v_arg_3741_);
                                                                lean_del_object(v___x_3722_);
                                                                lean_dec(v_stx_3720_);
                                                                lean_dec_ref(v_i_3714_);
                                                                lean_dec_ref(v___f_3710_);
                                                                v___x_3760_ = lean_box(0);
                                                                return v___x_3760_;
                                                            } else {
                                                                v___x_3761_ = lean_apply_1(
                                                                    v___f_3710_,
                                                                    v_arg_3741_,
                                                                );
                                                                v___y_3725_ = v___x_3761_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_3747_);
                                                            v___x_3762_ = lean_apply_1(
                                                                v___f_3710_,
                                                                v_arg_3741_,
                                                            );
                                                            v___y_3725_ = v___x_3762_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_3747_);
                                                        v___x_3763_ =
                                                            lean_apply_1(v___f_3710_, v_arg_3741_);
                                                        v___y_3725_ = v___x_3763_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_3747_);
                                                    v___x_3764_ =
                                                        lean_apply_1(v___f_3710_, v_arg_3741_);
                                                    v___y_3725_ = v___x_3764_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v___x_3747_);
                                                v___x_3765_ =
                                                    lean_apply_1(v___f_3710_, v_arg_3741_);
                                                v___y_3725_ = v___x_3765_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3747_);
                                            v___x_3766_ = lean_apply_1(v___f_3710_, v_arg_3741_);
                                            v___y_3725_ = v___x_3766_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3742_);
                                    lean_dec_ref(v_arg_3741_);
                                    v___x_3767_ = lean_apply_1(v___f_3710_, v_arg_3719_);
                                    v___y_3725_ = v___x_3767_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3732_);
                            v___x_3768_ = lean_apply_1(v___f_3710_, v_arg_3719_);
                            v___y_3725_ = v___x_3768_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3732_);
                        v___x_3769_ = lean_apply_1(v___f_3710_, v_arg_3719_);
                        v___y_3725_ = v___x_3769_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3732_);
                    v___x_3770_ = lean_apply_1(v___f_3710_, v_arg_3719_);
                    v___y_3725_ = v___x_3770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v___y_3725_) == 0 {
                    lean_del_object(v___x_3722_);
                    lean_dec(v_stx_3720_);
                    lean_dec_ref(v_i_3714_);
                    v___x_3726_ = lean_box(0);
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
                        lean_ctor_set(v___x_3722_, 0, v___x_3728_);
                        v___x_3730_ = v___x_3722_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
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
    mut v___f_3774_: *mut LeanObject,
    mut v_x_3775_: *mut LeanObject,
    mut v_info_3776_: *mut LeanObject,
    mut v_x_3777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3778_: *mut LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_Lean_Linter_List_numericalWidths___lam__1(
        v___f_3774_,
        v_x_3775_,
        v_info_3776_,
        v_x_3777_,
    );
    lean_dec_ref(v_x_3777_);
    lean_dec_ref(v_x_3775_);
    return v_res_3778_;
}
pub unsafe fn l_Lean_Linter_List_numericalWidths(
    mut v_t_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___f_3783_ = l_Lean_Linter_List_numericalWidths___closed__1;
    v___x_3784_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3783_, v_t_3782_);
    v___x_3785_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3786_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3784_, v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Linter_List_bitVecWidths___lam__0(
    mut v_x_3790_: *mut LeanObject,
    mut v_info_3791_: *mut LeanObject,
    mut v_x_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_unused_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_3791_) == 1 {
                    v_i_3793_ = lean_ctor_get(v_info_3791_, 0);
                    lean_inc_ref(v_i_3793_);
                    v_expr_3794_ = lean_ctor_get(v_i_3793_, 3);
                    lean_inc_ref(v_expr_3794_);
                    v___x_3795_ = l_Lean_Expr_cleanupAnnotations(v_expr_3794_);
                    v___x_3796_ = l_Lean_Expr_isApp(v___x_3795_);
                    if v___x_3796_ == 0 {
                        lean_dec_ref(v___x_3795_);
                        lean_dec_ref(v_i_3793_);
                        lean_dec_ref_known(v_info_3791_, 1);
                        v___x_3797_ = lean_box(0);
                        return v___x_3797_;
                    } else {
                        v_arg_3798_ = lean_ctor_get(v___x_3795_, 1);
                        lean_inc_ref(v_arg_3798_);
                        v___x_3799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3795_);
                        v___x_3800_ = l_Lean_Linter_List_bitVecWidths___lam__0___closed__1;
                        v___x_3801_ = l_Lean_Expr_isConstOf(v___x_3799_, v___x_3800_);
                        lean_dec_ref(v___x_3799_);
                        if v___x_3801_ == 0 {
                            lean_dec_ref(v_arg_3798_);
                            lean_dec_ref(v_i_3793_);
                            lean_dec_ref_known(v_info_3791_, 1);
                            v___x_3802_ = lean_box(0);
                            return v___x_3802_;
                        } else {
                            v_stx_3803_ = l_Lean_Elab_Info_stx(v_info_3791_);
                            v_isSharedCheck_3814_ = (!lean_is_exclusive(v_info_3791_)) as u8;
                            if v_isSharedCheck_3814_ == 0 {
                                v_unused_3815_ = lean_ctor_get(v_info_3791_, 0);
                                lean_dec(v_unused_3815_);
                                v___x_3805_ = v_info_3791_;
                                v_isShared_3806_ = v_isSharedCheck_3814_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_info_3791_);
                                v___x_3805_ = lean_box(0);
                                v_isShared_3806_ = v_isSharedCheck_3814_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_info_3791_);
                    v___x_3816_ = lean_box(0);
                    return v___x_3816_;
                }
            }
            1 => {
                v___x_3807_ = lean_box(0);
                v___x_3808_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3808_, 0, v_arg_3798_);
                lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                v___x_3809_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
                v___x_3810_ =
                    l_List_filterMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__0(
                        v_i_3793_,
                        v_stx_3803_,
                        v___x_3808_,
                        v___x_3809_,
                    );
                if v_isShared_3806_ == 0 {
                    lean_ctor_set(v___x_3805_, 0, v___x_3810_);
                    v___x_3812_ = v___x_3805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
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
    mut v_x_3817_: *mut LeanObject,
    mut v_info_3818_: *mut LeanObject,
    mut v_x_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3820_: *mut LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Lean_Linter_List_bitVecWidths___lam__0(v_x_3817_, v_info_3818_, v_x_3819_);
    lean_dec_ref(v_x_3819_);
    lean_dec_ref(v_x_3817_);
    return v_res_3820_;
}
pub unsafe fn l_Lean_Linter_List_bitVecWidths(mut v_t_3822_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    v___f_3823_ = l_Lean_Linter_List_bitVecWidths___closed__0;
    v___x_3824_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3823_, v_t_3822_);
    v___x_3825_ = l_Lean_Linter_List_numericalIndices___lam__2___closed__0;
    v___x_3826_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_List_numericalIndices_spec__1(v___x_3824_, v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3828_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0;
    v___x_3829_ = lean_string_utf8_byte_size(v___x_3828_);
    return v___x_3829_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1(
    mut v_s_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_unused_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3831_ = lean_ctor_get(v_s_3830_, 0);
                v_startInclusive_3832_ = lean_ctor_get(v_s_3830_, 1);
                v_endExclusive_3833_ = lean_ctor_get(v_s_3830_, 2);
                v___x_3834_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__0;
                v___x_3835_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__1___closed__1);
                v___x_3836_ = lean_nat_sub(v_endExclusive_3833_, v_startInclusive_3832_);
                v___x_3837_ = lean_nat_dec_le(v___x_3835_, v___x_3836_);
                if v___x_3837_ == 0 {
                    lean_dec(v___x_3836_);
                    return v_s_3830_;
                } else {
                    v___x_3838_ = lean_unsigned_to_nat(0);
                    v___x_3839_ = lean_nat_sub(v___x_3836_, v___x_3835_);
                    lean_dec(v___x_3836_);
                    v___x_3840_ = lean_nat_add(v_startInclusive_3832_, v___x_3839_);
                    v___x_3841_ = lean_string_memcmp(
                        v_str_3831_,
                        v___x_3834_,
                        v___x_3840_,
                        v___x_3838_,
                        v___x_3835_,
                    );
                    lean_dec(v___x_3840_);
                    if v___x_3841_ == 0 {
                        lean_dec(v___x_3839_);
                        return v_s_3830_;
                    } else {
                        lean_inc(v_startInclusive_3832_);
                        lean_inc_ref(v_str_3831_);
                        v___x_3842_ = l_String_Slice_pos_x21(v_s_3830_, v___x_3839_);
                        lean_dec(v___x_3839_);
                        v_isSharedCheck_3850_ = (!lean_is_exclusive(v_s_3830_)) as u8;
                        if v_isSharedCheck_3850_ == 0 {
                            v_unused_3851_ = lean_ctor_get(v_s_3830_, 2);
                            lean_dec(v_unused_3851_);
                            v_unused_3852_ = lean_ctor_get(v_s_3830_, 1);
                            lean_dec(v_unused_3852_);
                            v_unused_3853_ = lean_ctor_get(v_s_3830_, 0);
                            lean_dec(v_unused_3853_);
                            v___x_3844_ = v_s_3830_;
                            v_isShared_3845_ = v_isSharedCheck_3850_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_3830_);
                            v___x_3844_ = lean_box(0);
                            v_isShared_3845_ = v_isSharedCheck_3850_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3846_ = lean_nat_add(v_startInclusive_3832_, v___x_3842_);
                lean_dec(v___x_3842_);
                if v_isShared_3845_ == 0 {
                    lean_ctor_set(v___x_3844_, 2, v___x_3846_);
                    v___x_3848_ = v___x_3844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_str_3831_);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_startInclusive_3832_);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 2, v___x_3846_);
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
-> *mut LeanObject {
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    v___x_3855_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0;
    v___x_3856_ = lean_string_utf8_byte_size(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2(
    mut v_s_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut v_unused_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3858_ = lean_ctor_get(v_s_3857_, 0);
                v_startInclusive_3859_ = lean_ctor_get(v_s_3857_, 1);
                v_endExclusive_3860_ = lean_ctor_get(v_s_3857_, 2);
                v___x_3861_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__0;
                v___x_3862_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__2___closed__1);
                v___x_3863_ = lean_nat_sub(v_endExclusive_3860_, v_startInclusive_3859_);
                v___x_3864_ = lean_nat_dec_le(v___x_3862_, v___x_3863_);
                if v___x_3864_ == 0 {
                    lean_dec(v___x_3863_);
                    return v_s_3857_;
                } else {
                    v___x_3865_ = lean_unsigned_to_nat(0);
                    v___x_3866_ = lean_nat_sub(v___x_3863_, v___x_3862_);
                    lean_dec(v___x_3863_);
                    v___x_3867_ = lean_nat_add(v_startInclusive_3859_, v___x_3866_);
                    v___x_3868_ = lean_string_memcmp(
                        v_str_3858_,
                        v___x_3861_,
                        v___x_3867_,
                        v___x_3865_,
                        v___x_3862_,
                    );
                    lean_dec(v___x_3867_);
                    if v___x_3868_ == 0 {
                        lean_dec(v___x_3866_);
                        return v_s_3857_;
                    } else {
                        lean_inc(v_startInclusive_3859_);
                        lean_inc_ref(v_str_3858_);
                        v___x_3869_ = l_String_Slice_pos_x21(v_s_3857_, v___x_3866_);
                        lean_dec(v___x_3866_);
                        v_isSharedCheck_3877_ = (!lean_is_exclusive(v_s_3857_)) as u8;
                        if v_isSharedCheck_3877_ == 0 {
                            v_unused_3878_ = lean_ctor_get(v_s_3857_, 2);
                            lean_dec(v_unused_3878_);
                            v_unused_3879_ = lean_ctor_get(v_s_3857_, 1);
                            lean_dec(v_unused_3879_);
                            v_unused_3880_ = lean_ctor_get(v_s_3857_, 0);
                            lean_dec(v_unused_3880_);
                            v___x_3871_ = v_s_3857_;
                            v_isShared_3872_ = v_isSharedCheck_3877_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_3857_);
                            v___x_3871_ = lean_box(0);
                            v_isShared_3872_ = v_isSharedCheck_3877_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3873_ = lean_nat_add(v_startInclusive_3859_, v___x_3869_);
                lean_dec(v___x_3869_);
                if v_isShared_3872_ == 0 {
                    lean_ctor_set(v___x_3871_, 2, v___x_3873_);
                    v___x_3875_ = v___x_3871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_str_3858_);
                    lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_startInclusive_3859_);
                    lean_ctor_set(v_reuseFailAlloc_3876_, 2, v___x_3873_);
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
-> *mut LeanObject {
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v___x_3882_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0;
    v___x_3883_ = lean_string_utf8_byte_size(v___x_3882_);
    return v___x_3883_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3(
    mut v_s_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v_unused_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3885_ = lean_ctor_get(v_s_3884_, 0);
                v_startInclusive_3886_ = lean_ctor_get(v_s_3884_, 1);
                v_endExclusive_3887_ = lean_ctor_get(v_s_3884_, 2);
                v___x_3888_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__0;
                v___x_3889_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__3___closed__1);
                v___x_3890_ = lean_nat_sub(v_endExclusive_3887_, v_startInclusive_3886_);
                v___x_3891_ = lean_nat_dec_le(v___x_3889_, v___x_3890_);
                if v___x_3891_ == 0 {
                    lean_dec(v___x_3890_);
                    return v_s_3884_;
                } else {
                    v___x_3892_ = lean_unsigned_to_nat(0);
                    v___x_3893_ = lean_nat_sub(v___x_3890_, v___x_3889_);
                    lean_dec(v___x_3890_);
                    v___x_3894_ = lean_nat_add(v_startInclusive_3886_, v___x_3893_);
                    v___x_3895_ = lean_string_memcmp(
                        v_str_3885_,
                        v___x_3888_,
                        v___x_3894_,
                        v___x_3892_,
                        v___x_3889_,
                    );
                    lean_dec(v___x_3894_);
                    if v___x_3895_ == 0 {
                        lean_dec(v___x_3893_);
                        return v_s_3884_;
                    } else {
                        lean_inc(v_startInclusive_3886_);
                        lean_inc_ref(v_str_3885_);
                        v___x_3896_ = l_String_Slice_pos_x21(v_s_3884_, v___x_3893_);
                        lean_dec(v___x_3893_);
                        v_isSharedCheck_3904_ = (!lean_is_exclusive(v_s_3884_)) as u8;
                        if v_isSharedCheck_3904_ == 0 {
                            v_unused_3905_ = lean_ctor_get(v_s_3884_, 2);
                            lean_dec(v_unused_3905_);
                            v_unused_3906_ = lean_ctor_get(v_s_3884_, 1);
                            lean_dec(v_unused_3906_);
                            v_unused_3907_ = lean_ctor_get(v_s_3884_, 0);
                            lean_dec(v_unused_3907_);
                            v___x_3898_ = v_s_3884_;
                            v_isShared_3899_ = v_isSharedCheck_3904_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_3884_);
                            v___x_3898_ = lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3904_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3900_ = lean_nat_add(v_startInclusive_3886_, v___x_3896_);
                lean_dec(v___x_3896_);
                if v_isShared_3899_ == 0 {
                    lean_ctor_set(v___x_3898_, 2, v___x_3900_);
                    v___x_3902_ = v___x_3898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_str_3885_);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_startInclusive_3886_);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 2, v___x_3900_);
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
-> *mut LeanObject {
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3909_ =
        l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0;
    v___x_3910_ = lean_string_utf8_byte_size(v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4(
    mut v_s_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3912_ = lean_ctor_get(v_s_3911_, 0);
                v_startInclusive_3913_ = lean_ctor_get(v_s_3911_, 1);
                v_endExclusive_3914_ = lean_ctor_get(v_s_3911_, 2);
                v___x_3915_ = l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__0;
                v___x_3916_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1_once), _init_l_String_Slice_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__4___closed__1);
                v___x_3917_ = lean_nat_sub(v_endExclusive_3914_, v_startInclusive_3913_);
                v___x_3918_ = lean_nat_dec_le(v___x_3916_, v___x_3917_);
                if v___x_3918_ == 0 {
                    lean_dec(v___x_3917_);
                    return v_s_3911_;
                } else {
                    v___x_3919_ = lean_unsigned_to_nat(0);
                    v___x_3920_ = lean_nat_sub(v___x_3917_, v___x_3916_);
                    lean_dec(v___x_3917_);
                    v___x_3921_ = lean_nat_add(v_startInclusive_3913_, v___x_3920_);
                    v___x_3922_ = lean_string_memcmp(
                        v_str_3912_,
                        v___x_3915_,
                        v___x_3921_,
                        v___x_3919_,
                        v___x_3916_,
                    );
                    lean_dec(v___x_3921_);
                    if v___x_3922_ == 0 {
                        lean_dec(v___x_3920_);
                        return v_s_3911_;
                    } else {
                        lean_inc(v_startInclusive_3913_);
                        lean_inc_ref(v_str_3912_);
                        v___x_3923_ = l_String_Slice_pos_x21(v_s_3911_, v___x_3920_);
                        lean_dec(v___x_3920_);
                        v_isSharedCheck_3931_ = (!lean_is_exclusive(v_s_3911_)) as u8;
                        if v_isSharedCheck_3931_ == 0 {
                            v_unused_3932_ = lean_ctor_get(v_s_3911_, 2);
                            lean_dec(v_unused_3932_);
                            v_unused_3933_ = lean_ctor_get(v_s_3911_, 1);
                            lean_dec(v_unused_3933_);
                            v_unused_3934_ = lean_ctor_get(v_s_3911_, 0);
                            lean_dec(v_unused_3934_);
                            v___x_3925_ = v_s_3911_;
                            v_isShared_3926_ = v_isSharedCheck_3931_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_3911_);
                            v___x_3925_ = lean_box(0);
                            v_isShared_3926_ = v_isSharedCheck_3931_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3927_ = lean_nat_add(v_startInclusive_3913_, v___x_3923_);
                lean_dec(v___x_3923_);
                if v_isShared_3926_ == 0 {
                    lean_ctor_set(v___x_3925_, 2, v___x_3927_);
                    v___x_3929_ = v___x_3925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_str_3912_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_startInclusive_3913_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 2, v___x_3927_);
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
-> *mut LeanObject {
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    v___x_3936_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0;
    v___x_3937_ = lean_string_utf8_byte_size(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(
    mut v_s_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_unused_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3939_ = lean_ctor_get(v_s_3938_, 0);
                v_startInclusive_3940_ = lean_ctor_get(v_s_3938_, 1);
                v_endExclusive_3941_ = lean_ctor_get(v_s_3938_, 2);
                v___x_3942_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__0;
                v___x_3943_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg___closed__1);
                v___x_3944_ = lean_nat_sub(v_endExclusive_3941_, v_startInclusive_3940_);
                v___x_3945_ = lean_nat_dec_le(v___x_3943_, v___x_3944_);
                if v___x_3945_ == 0 {
                    lean_dec(v___x_3944_);
                    return v_s_3938_;
                } else {
                    v___x_3946_ = lean_unsigned_to_nat(0);
                    v___x_3947_ = lean_nat_sub(v___x_3944_, v___x_3943_);
                    lean_dec(v___x_3944_);
                    v___x_3948_ = lean_nat_add(v_startInclusive_3940_, v___x_3947_);
                    v___x_3949_ = lean_string_memcmp(
                        v_str_3939_,
                        v___x_3942_,
                        v___x_3948_,
                        v___x_3946_,
                        v___x_3943_,
                    );
                    lean_dec(v___x_3948_);
                    if v___x_3949_ == 0 {
                        lean_dec(v___x_3947_);
                        return v_s_3938_;
                    } else {
                        lean_inc(v_startInclusive_3940_);
                        lean_inc_ref(v_str_3939_);
                        v___x_3950_ = l_String_Slice_pos_x21(v_s_3938_, v___x_3947_);
                        lean_dec(v___x_3947_);
                        v_isSharedCheck_3958_ = (!lean_is_exclusive(v_s_3938_)) as u8;
                        if v_isSharedCheck_3958_ == 0 {
                            v_unused_3959_ = lean_ctor_get(v_s_3938_, 2);
                            lean_dec(v_unused_3959_);
                            v_unused_3960_ = lean_ctor_get(v_s_3938_, 1);
                            lean_dec(v_unused_3960_);
                            v_unused_3961_ = lean_ctor_get(v_s_3938_, 0);
                            lean_dec(v_unused_3961_);
                            v___x_3952_ = v_s_3938_;
                            v_isShared_3953_ = v_isSharedCheck_3958_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_3938_);
                            v___x_3952_ = lean_box(0);
                            v_isShared_3953_ = v_isSharedCheck_3958_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3954_ = lean_nat_add(v_startInclusive_3940_, v___x_3950_);
                lean_dec(v___x_3950_);
                if v_isShared_3953_ == 0 {
                    lean_ctor_set(v___x_3952_, 2, v___x_3954_);
                    v___x_3956_ = v___x_3952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_str_3939_);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_startInclusive_3940_);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 2, v___x_3954_);
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
    mut v_s_3962_: *mut LeanObject,
    mut v_pat_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3964_ = lean_unsigned_to_nat(0);
    v___x_3965_ = lean_string_utf8_byte_size(v_s_3962_);
    v___x_3966_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3966_, 0, v_s_3962_);
    lean_ctor_set(v___x_3966_, 1, v___x_3964_);
    lean_ctor_set(v___x_3966_, 2, v___x_3965_);
    v___x_3967_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0___boxed(
    mut v_s_3968_: *mut LeanObject,
    mut v_pat_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3970_: *mut LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0(
        v_s_3968_,
        v_pat_3969_,
    );
    lean_dec_ref(v_pat_3969_);
    return v_res_3970_;
}
pub unsafe fn l_Lean_Linter_List_stripBinderName(
    mut v_s_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
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
    v_str_3978_ = lean_ctor_get(v___x_3977_, 0);
    lean_inc_ref(v_str_3978_);
    v_startInclusive_3979_ = lean_ctor_get(v___x_3977_, 1);
    lean_inc(v_startInclusive_3979_);
    v_endExclusive_3980_ = lean_ctor_get(v___x_3977_, 2);
    lean_inc(v_endExclusive_3980_);
    lean_dec_ref(v___x_3977_);
    v___x_3981_ =
        lean_string_utf8_extract(v_str_3978_, v_startInclusive_3979_, v_endExclusive_3980_);
    lean_dec(v_endExclusive_3980_);
    lean_dec(v_startInclusive_3979_);
    lean_dec_ref(v_str_3978_);
    return v___x_3981_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(
    mut v_pat_3982_: *mut LeanObject,
    mut v_s_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    v___x_3984_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___redArg(v_s_3983_);
    return v___x_3984_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0___boxed(
    mut v_pat_3985_: *mut LeanObject,
    mut v_s_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lean_Linter_List_stripBinderName_spec__0_spec__0(v_pat_3985_, v_s_3986_);
    lean_dec_ref(v_pat_3985_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
    mut v___y_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    v___x_4040_ = lean_st_ref_get(v___y_4038_);
    v_infoState_4041_ = lean_ctor_get(v___x_4040_, 8);
    lean_inc_ref(v_infoState_4041_);
    lean_dec(v___x_4040_);
    v_trees_4042_ = lean_ctor_get(v_infoState_4041_, 2);
    lean_inc_ref(v_trees_4042_);
    lean_dec_ref(v_infoState_4041_);
    v___x_4043_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4043_, 0, v_trees_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg___boxed(
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4046_: *mut LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
        v___y_4044_,
    );
    lean_dec(v___y_4044_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(
        v___y_4048_,
    );
    return v___x_4050_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___boxed(
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4054_: *mut LeanObject = core::ptr::null_mut();
    v_res_4054_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0(
        v___y_4051_,
        v___y_4052_,
    );
    lean_dec(v___y_4052_);
    lean_dec_ref(v___y_4051_);
    return v_res_4054_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(
    mut v_opts_4055_: *mut LeanObject,
    mut v_opt_4056_: *mut LeanObject,
) -> u8 {
    let mut v_name_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v_name_4057_ = lean_ctor_get(v_opt_4056_, 0);
    v_defValue_4058_ = lean_ctor_get(v_opt_4056_, 1);
    v_map_4059_ = lean_ctor_get(v_opts_4055_, 0);
    v___x_4060_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4059_,
            v_name_4057_,
        );
    if lean_obj_tag(v___x_4060_) == 0 {
        let mut v___x_4061_: u8 = 0;
        v___x_4061_ = (lean_unbox(v_defValue_4058_) as u8);
        return v___x_4061_;
    } else {
        let mut v_val_4062_: *mut LeanObject = core::ptr::null_mut();
        v_val_4062_ = lean_ctor_get(v___x_4060_, 0);
        lean_inc(v_val_4062_);
        lean_dec_ref_known(v___x_4060_, 1);
        if lean_obj_tag(v_val_4062_) == 1 {
            let mut v_v_4063_: u8 = 0;
            v_v_4063_ = lean_ctor_get_uint8(v_val_4062_, 0 as u32);
            lean_dec_ref_known(v_val_4062_, 0);
            return v_v_4063_;
        } else {
            let mut v___x_4064_: u8 = 0;
            lean_dec(v_val_4062_);
            v___x_4064_ = (lean_unbox(v_defValue_4058_) as u8);
            return v___x_4064_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9___boxed(
    mut v_opts_4065_: *mut LeanObject,
    mut v_opt_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4067_: u8 = 0;
    let mut v_r_4068_: *mut LeanObject = core::ptr::null_mut();
    v_res_4067_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_4065_, v_opt_4066_);
    lean_dec_ref(v_opt_4066_);
    lean_dec_ref(v_opts_4065_);
    v_r_4068_ = lean_box((v_res_4067_) as usize);
    return v_r_4068_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(
    mut v___y_4070_: u8,
    mut v_suppressElabErrors_4071_: u8,
    mut v_x_4072_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4072_) == 1 {
        let mut v_pre_4073_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4073_ = lean_ctor_get(v_x_4072_, 0);
        if lean_obj_tag(v_pre_4073_) == 0 {
            let mut v_str_4074_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4076_: u8 = 0;
            v_str_4074_ = lean_ctor_get(v_x_4072_, 1);
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
    mut v___y_4077_: *mut LeanObject,
    mut v_suppressElabErrors_4078_: *mut LeanObject,
    mut v_x_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_12587__boxed_4080_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4081_: u8 = 0;
    let mut v_res_4082_: u8 = 0;
    let mut v_r_4083_: *mut LeanObject = core::ptr::null_mut();
    v___y_12587__boxed_4080_ = (lean_unbox(v___y_4077_) as u8);
    v_suppressElabErrors_boxed_4081_ = (lean_unbox(v_suppressElabErrors_4078_) as u8);
    v_res_4082_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0(v___y_12587__boxed_4080_, v_suppressElabErrors_boxed_4081_, v_x_4079_);
    lean_dec(v_x_4079_);
    v_r_4083_ = lean_box((v_res_4082_) as usize);
    return v_r_4083_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4084_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__0);
    v___x_4086_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4086_, 0, v___x_4085_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    v___x_4087_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
    v___x_4088_ = lean_unsigned_to_nat(0);
    v___x_4089_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4089_, 0, v___x_4088_);
    lean_ctor_set(v___x_4089_, 1, v___x_4088_);
    lean_ctor_set(v___x_4089_, 2, v___x_4088_);
    lean_ctor_set(v___x_4089_, 3, v___x_4088_);
    lean_ctor_set(v___x_4089_, 4, v___x_4087_);
    lean_ctor_set(v___x_4089_, 5, v___x_4087_);
    lean_ctor_set(v___x_4089_, 6, v___x_4087_);
    lean_ctor_set(v___x_4089_, 7, v___x_4087_);
    lean_ctor_set(v___x_4089_, 8, v___x_4087_);
    lean_ctor_set(v___x_4089_, 9, v___x_4087_);
    return v___x_4089_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v___x_4090_ = lean_unsigned_to_nat(32);
    v___x_4091_ = lean_mk_empty_array_with_capacity(v___x_4090_);
    v___x_4092_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4092_, 0, v___x_4091_);
    return v___x_4092_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4093_: usize = 0;
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4093_ = 5usize;
    v___x_4094_ = lean_unsigned_to_nat(0);
    v___x_4095_ = lean_unsigned_to_nat(32);
    v___x_4096_ = lean_mk_empty_array_with_capacity(v___x_4095_);
    v___x_4097_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__3);
    v___x_4098_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4098_, 0, v___x_4097_);
    lean_ctor_set(v___x_4098_, 1, v___x_4096_);
    lean_ctor_set(v___x_4098_, 2, v___x_4094_);
    lean_ctor_set(v___x_4098_, 3, v___x_4094_);
    lean_ctor_set_usize(v___x_4098_, 4, v___x_4093_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    v___x_4099_ = lean_box(1);
    v___x_4100_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__4);
    v___x_4101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__1);
    v___x_4102_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4102_, 0, v___x_4101_);
    lean_ctor_set(v___x_4102_, 1, v___x_4100_);
    lean_ctor_set(v___x_4102_, 2, v___x_4099_);
    return v___x_4102_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(
    mut v_msgData_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    v___x_4106_ = lean_st_ref_get(v___y_4104_);
    v_env_4107_ = lean_ctor_get(v___x_4106_, 0);
    lean_inc_ref(v_env_4107_);
    lean_dec(v___x_4106_);
    v___x_4108_ = lean_st_ref_get(v___y_4104_);
    v_scopes_4109_ = lean_ctor_get(v___x_4108_, 2);
    lean_inc(v_scopes_4109_);
    lean_dec(v___x_4108_);
    v___x_4110_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_4111_ = l_List_head_x21___redArg(v___x_4110_, v_scopes_4109_);
    lean_dec(v_scopes_4109_);
    v_opts_4112_ = lean_ctor_get(v___x_4111_, 1);
    lean_inc_ref(v_opts_4112_);
    lean_dec(v___x_4111_);
    v___x_4113_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__2);
    v___x_4114_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___closed__5);
    v___x_4115_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4115_, 0, v_env_4107_);
    lean_ctor_set(v___x_4115_, 1, v___x_4113_);
    lean_ctor_set(v___x_4115_, 2, v___x_4114_);
    lean_ctor_set(v___x_4115_, 3, v_opts_4112_);
    v___x_4116_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4116_, 0, v___x_4115_);
    lean_ctor_set(v___x_4116_, 1, v_msgData_4103_);
    v___x_4117_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4117_, 0, v___x_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg___boxed(
    mut v_msgData_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4121_: *mut LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_4118_, v___y_4119_);
    lean_dec(v___y_4119_);
    return v_res_4121_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(
    mut v_ref_4123_: *mut LeanObject,
    mut v_msgData_4124_: *mut LeanObject,
    mut v_severity_4125_: u8,
    mut v_isSilent_4126_: u8,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: u8 = 0;
    let mut v___y_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4135_: u8 = 0;
    let mut v___y_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_a_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_a_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v___y_4194_: u8 = 0;
    let mut v___y_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: u8 = 0;
    let mut v___y_4197_: u8 = 0;
    let mut v___y_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4201_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u8 = 0;
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v___y_4222_: u8 = 0;
    let mut v___y_4223_: u8 = 0;
    let mut v___y_4224_: u8 = 0;
    let mut v___y_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4230_: u8 = 0;
    let mut v___y_4231_: u8 = 0;
    let mut v___y_4232_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___x_4247_: u8 = 0;
    let mut v___y_4249_: u8 = 0;
    let mut v___y_4250_: u8 = 0;
    let mut v___y_4251_: u8 = 0;
    let mut v___y_4253_: u8 = 0;
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_4124_);
                    v___x_4266_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4124_);
                    v___y_4253_ = v___x_4266_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_4139_ = l_Lean_Elab_Command_getScope___redArg(v___y_4138_);
                if lean_obj_tag(v___x_4139_) == 0 {
                    v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
                    lean_inc(v_a_4140_);
                    lean_dec_ref_known(v___x_4139_, 1);
                    v___x_4141_ = l_Lean_Elab_Command_getScope___redArg(v___y_4138_);
                    if lean_obj_tag(v___x_4141_) == 0 {
                        v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
                        v_isSharedCheck_4176_ = (!lean_is_exclusive(v___x_4141_)) as u8;
                        if v_isSharedCheck_4176_ == 0 {
                            v___x_4144_ = v___x_4141_;
                            v_isShared_4145_ = v_isSharedCheck_4176_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4142_);
                            lean_dec(v___x_4141_);
                            v___x_4144_ = lean_box(0);
                            v_isShared_4145_ = v_isSharedCheck_4176_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4140_);
                        lean_dec(v___y_4137_);
                        lean_dec_ref(v___y_4133_);
                        lean_dec_ref(v___y_4131_);
                        v_a_4177_ = lean_ctor_get(v___x_4141_, 0);
                        v_isSharedCheck_4184_ = (!lean_is_exclusive(v___x_4141_)) as u8;
                        if v_isSharedCheck_4184_ == 0 {
                            v___x_4179_ = v___x_4141_;
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4177_);
                            lean_dec(v___x_4141_);
                            v___x_4179_ = lean_box(0);
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_4137_);
                    lean_dec_ref(v___y_4133_);
                    lean_dec_ref(v___y_4131_);
                    v_a_4185_ = lean_ctor_get(v___x_4139_, 0);
                    v_isSharedCheck_4192_ = (!lean_is_exclusive(v___x_4139_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v___x_4187_ = v___x_4139_;
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4185_);
                        lean_dec(v___x_4139_);
                        v___x_4187_ = lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4146_ = lean_st_ref_take(v___y_4138_);
                v_currNamespace_4147_ = lean_ctor_get(v_a_4140_, 2);
                lean_inc(v_currNamespace_4147_);
                lean_dec(v_a_4140_);
                v_openDecls_4148_ = lean_ctor_get(v_a_4142_, 3);
                lean_inc(v_openDecls_4148_);
                lean_dec(v_a_4142_);
                v_env_4149_ = lean_ctor_get(v___x_4146_, 0);
                v_messages_4150_ = lean_ctor_get(v___x_4146_, 1);
                v_scopes_4151_ = lean_ctor_get(v___x_4146_, 2);
                v_usedQuotCtxts_4152_ = lean_ctor_get(v___x_4146_, 3);
                v_nextMacroScope_4153_ = lean_ctor_get(v___x_4146_, 4);
                v_maxRecDepth_4154_ = lean_ctor_get(v___x_4146_, 5);
                v_ngen_4155_ = lean_ctor_get(v___x_4146_, 6);
                v_auxDeclNGen_4156_ = lean_ctor_get(v___x_4146_, 7);
                v_infoState_4157_ = lean_ctor_get(v___x_4146_, 8);
                v_traceState_4158_ = lean_ctor_get(v___x_4146_, 9);
                v_snapshotTasks_4159_ = lean_ctor_get(v___x_4146_, 10);
                v_isSharedCheck_4175_ = (!lean_is_exclusive(v___x_4146_)) as u8;
                if v_isSharedCheck_4175_ == 0 {
                    v___x_4161_ = v___x_4146_;
                    v_isShared_4162_ = v_isSharedCheck_4175_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4159_);
                    lean_inc(v_traceState_4158_);
                    lean_inc(v_infoState_4157_);
                    lean_inc(v_auxDeclNGen_4156_);
                    lean_inc(v_ngen_4155_);
                    lean_inc(v_maxRecDepth_4154_);
                    lean_inc(v_nextMacroScope_4153_);
                    lean_inc(v_usedQuotCtxts_4152_);
                    lean_inc(v_scopes_4151_);
                    lean_inc(v_messages_4150_);
                    lean_inc(v_env_4149_);
                    lean_dec(v___x_4146_);
                    v___x_4161_ = lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4163_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4163_, 0, v_currNamespace_4147_);
                lean_ctor_set(v___x_4163_, 1, v_openDecls_4148_);
                v___x_4164_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                lean_ctor_set(v___x_4164_, 1, v___y_4133_);
                lean_inc_ref(v___y_4136_);
                lean_inc_ref(v___y_4134_);
                v___x_4165_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4165_, 0, v___y_4134_);
                lean_ctor_set(v___x_4165_, 1, v___y_4131_);
                lean_ctor_set(v___x_4165_, 2, v___y_4137_);
                lean_ctor_set(v___x_4165_, 3, v___y_4136_);
                lean_ctor_set(v___x_4165_, 4, v___x_4164_);
                lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4135_,
                );
                lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4132_,
                );
                lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4126_,
                );
                v___x_4166_ = l_Lean_MessageLog_add(v___x_4165_, v_messages_4150_);
                if v_isShared_4162_ == 0 {
                    lean_ctor_set(v___x_4161_, 1, v___x_4166_);
                    v___x_4168_ = v___x_4161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_env_4149_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4166_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_scopes_4151_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 3, v_usedQuotCtxts_4152_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 4, v_nextMacroScope_4153_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 5, v_maxRecDepth_4154_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 6, v_ngen_4155_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 7, v_auxDeclNGen_4156_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 8, v_infoState_4157_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 9, v_traceState_4158_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 10, v_snapshotTasks_4159_);
                    v___x_4168_ = v_reuseFailAlloc_4174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4169_ = lean_st_ref_set(v___y_4138_, v___x_4168_);
                v___x_4170_ = lean_box(0);
                if v_isShared_4145_ == 0 {
                    lean_ctor_set(v___x_4144_, 0, v___x_4170_);
                    v___x_4172_ = v___x_4144_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
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
                    v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
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
                    v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4190_;
            }
            10 => {
                v_fileName_4199_ = lean_ctor_get(v___y_4127_, 0);
                v_fileMap_4200_ = lean_ctor_get(v___y_4127_, 1);
                v_suppressElabErrors_4201_ = lean_ctor_get_uint8(
                    v___y_4127_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_4202_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4124_,
                    );
                v___x_4203_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v___x_4202_, v___y_4128_);
                v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
                v_isSharedCheck_4220_ = (!lean_is_exclusive(v___x_4203_)) as u8;
                if v_isSharedCheck_4220_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    v_isShared_4207_ = v_isSharedCheck_4220_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_4204_);
                    lean_dec(v___x_4203_);
                    v___x_4206_ = lean_box(0);
                    v_isShared_4207_ = v_isSharedCheck_4220_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_4200_, 2);
                v___x_4208_ = l_Lean_FileMap_toPosition(v_fileMap_4200_, v___y_4195_);
                lean_dec(v___y_4195_);
                v___x_4209_ = l_Lean_FileMap_toPosition(v_fileMap_4200_, v___y_4198_);
                lean_dec(v___y_4198_);
                v___x_4210_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                v___x_4211_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___closed__0;
                if v_suppressElabErrors_4201_ == 0 {
                    lean_del_object(v___x_4206_);
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
                    v___x_4212_ = lean_box((v___y_4194_) as usize);
                    v___x_4213_ = lean_box((v_suppressElabErrors_4201_) as usize);
                    v___f_4214_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4214_, 0, v___x_4212_);
                    lean_closure_set(v___f_4214_, 1, v___x_4213_);
                    lean_inc(v_a_4204_);
                    v___x_4215_ = l_Lean_MessageData_hasTag(v___f_4214_, v_a_4204_);
                    if v___x_4215_ == 0 {
                        lean_dec_ref_known(v___x_4210_, 1);
                        lean_dec_ref(v___x_4208_);
                        lean_dec(v_a_4204_);
                        v___x_4216_ = lean_box(0);
                        if v_isShared_4207_ == 0 {
                            lean_ctor_set(v___x_4206_, 0, v___x_4216_);
                            v___x_4218_ = v___x_4206_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
                            v___x_4218_ = v_reuseFailAlloc_4219_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4206_);
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
                lean_dec(v___y_4225_);
                if lean_obj_tag(v___x_4227_) == 0 {
                    lean_inc(v___y_4226_);
                    v___y_4194_ = v___y_4222_;
                    v___y_4195_ = v___y_4226_;
                    v___y_4196_ = v___y_4223_;
                    v___y_4197_ = v___y_4224_;
                    v___y_4198_ = v___y_4226_;
                    state = 10;
                    continue;
                } else {
                    v_val_4228_ = lean_ctor_get(v___x_4227_, 0);
                    lean_inc(v_val_4228_);
                    lean_dec_ref_known(v___x_4227_, 1);
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
                if lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
                    lean_inc(v_a_4234_);
                    lean_dec_ref_known(v___x_4233_, 1);
                    v_ref_4235_ = l_Lean_replaceRef(v_ref_4123_, v_a_4234_);
                    lean_dec(v_a_4234_);
                    v___x_4236_ = l_Lean_Syntax_getPos_x3f(v_ref_4235_, v___y_4231_);
                    if lean_obj_tag(v___x_4236_) == 0 {
                        v___x_4237_ = lean_unsigned_to_nat(0);
                        v___y_4222_ = v___y_4230_;
                        v___y_4223_ = v___y_4232_;
                        v___y_4224_ = v___y_4231_;
                        v___y_4225_ = v_ref_4235_;
                        v___y_4226_ = v___x_4237_;
                        state = 13;
                        continue;
                    } else {
                        v_val_4238_ = lean_ctor_get(v___x_4236_, 0);
                        lean_inc(v_val_4238_);
                        lean_dec_ref_known(v___x_4236_, 1);
                        v___y_4222_ = v___y_4230_;
                        v___y_4223_ = v___y_4232_;
                        v___y_4224_ = v___y_4231_;
                        v___y_4225_ = v_ref_4235_;
                        v___y_4226_ = v_val_4238_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_4124_);
                    v_a_4239_ = lean_ctor_get(v___x_4233_, 0);
                    v_isSharedCheck_4246_ = (!lean_is_exclusive(v___x_4233_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___x_4233_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4239_);
                        lean_dec(v___x_4233_);
                        v___x_4241_ = lean_box(0);
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
                    v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
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
                    v_scopes_4255_ = lean_ctor_get(v___x_4254_, 2);
                    lean_inc(v_scopes_4255_);
                    lean_dec(v___x_4254_);
                    v___x_4256_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_4257_ = l_List_head_x21___redArg(v___x_4256_, v_scopes_4255_);
                    lean_dec(v_scopes_4255_);
                    v_opts_4258_ = lean_ctor_get(v___x_4257_, 1);
                    lean_inc_ref(v_opts_4258_);
                    lean_dec(v___x_4257_);
                    v___x_4259_ = 1;
                    v___x_4260_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4125_, v___x_4259_);
                    if v___x_4260_ == 0 {
                        lean_dec_ref(v_opts_4258_);
                        v___y_4249_ = v___y_4253_;
                        v___y_4250_ = v___y_4253_;
                        v___y_4251_ = v___x_4260_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4261_ = l_Lean_warningAsError;
                        v___x_4262_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__9(v_opts_4258_, v___x_4261_);
                        lean_dec_ref(v_opts_4258_);
                        v___y_4249_ = v___y_4253_;
                        v___y_4250_ = v___y_4253_;
                        v___y_4251_ = v___x_4262_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_4124_);
                    v___x_4263_ = lean_box(0);
                    v___x_4264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                    return v___x_4264_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3___boxed(
    mut v_ref_4267_: *mut LeanObject,
    mut v_msgData_4268_: *mut LeanObject,
    mut v_severity_4269_: *mut LeanObject,
    mut v_isSilent_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4274_: u8 = 0;
    let mut v_isSilent_boxed_4275_: u8 = 0;
    let mut v_res_4276_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4274_ = (lean_unbox(v_severity_4269_) as u8);
    v_isSilent_boxed_4275_ = (lean_unbox(v_isSilent_4270_) as u8);
    v_res_4276_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_4267_, v_msgData_4268_, v_severity_boxed_4274_, v_isSilent_boxed_4275_, v___y_4271_, v___y_4272_);
    lean_dec(v___y_4272_);
    lean_dec_ref(v___y_4271_);
    lean_dec(v_ref_4267_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(
    mut v_ref_4277_: *mut LeanObject,
    mut v_msgData_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = 1;
    v___x_4283_ = 0;
    v___x_4284_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3(v_ref_4277_, v_msgData_4278_, v___x_4282_, v___x_4283_, v___y_4279_, v___y_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2___boxed(
    mut v_ref_4285_: *mut LeanObject,
    mut v_msgData_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4290_: *mut LeanObject = core::ptr::null_mut();
    v_res_4290_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_ref_4285_, v_msgData_4286_, v___y_4287_, v___y_4288_);
    lean_dec(v___y_4288_);
    lean_dec_ref(v___y_4287_);
    lean_dec(v_ref_4285_);
    return v_res_4290_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__0;
    v___x_4293_ = l_Lean_stringToMessageData(v___x_4292_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__2;
    v___x_4296_ = l_Lean_stringToMessageData(v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
    mut v_linterOption_4297_: *mut LeanObject,
    mut v_stx_4298_: *mut LeanObject,
    mut v_msg_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_unused_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4303_ = lean_ctor_get(v_linterOption_4297_, 0);
                v_isSharedCheck_4320_ = (!lean_is_exclusive(v_linterOption_4297_)) as u8;
                if v_isSharedCheck_4320_ == 0 {
                    v_unused_4321_ = lean_ctor_get(v_linterOption_4297_, 1);
                    lean_dec(v_unused_4321_);
                    v___x_4305_ = v_linterOption_4297_;
                    v_isShared_4306_ = v_isSharedCheck_4320_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_4303_);
                    lean_dec(v_linterOption_4297_);
                    v___x_4305_ = lean_box(0);
                    v_isShared_4306_ = v_isSharedCheck_4320_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4307_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__1);
                lean_inc(v_name_4303_);
                v___x_4308_ = l_Lean_MessageData_ofName(v_name_4303_);
                if v_isShared_4306_ == 0 {
                    lean_ctor_set_tag(v___x_4305_, 7);
                    lean_ctor_set(v___x_4305_, 1, v___x_4308_);
                    lean_ctor_set(v___x_4305_, 0, v___x_4307_);
                    v___x_4310_ = v___x_4305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4307_);
                    lean_ctor_set(v_reuseFailAlloc_4319_, 1, v___x_4308_);
                    v___x_4310_ = v_reuseFailAlloc_4319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4311_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___closed__3);
                v___x_4312_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4312_, 0, v___x_4310_);
                lean_ctor_set(v___x_4312_, 1, v___x_4311_);
                v_disable_4313_ = l_Lean_MessageData_note(v___x_4312_);
                v___x_4314_ = l_Lean_Linter_linterMessageTag;
                v___x_4315_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4315_, 0, v_msg_4299_);
                lean_ctor_set(v___x_4315_, 1, v_disable_4313_);
                v___x_4316_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4316_, 0, v___x_4314_);
                lean_ctor_set(v___x_4316_, 1, v___x_4315_);
                v___x_4317_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4317_, 0, v_name_4303_);
                lean_ctor_set(v___x_4317_, 1, v___x_4316_);
                v___x_4318_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2(v_stx_4298_, v___x_4317_, v___y_4300_, v___y_4301_);
                return v___x_4318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2___boxed(
    mut v_linterOption_4322_: *mut LeanObject,
    mut v_stx_4323_: *mut LeanObject,
    mut v_msg_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4328_: *mut LeanObject = core::ptr::null_mut();
    v_res_4328_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
        v_linterOption_4322_,
        v_stx_4323_,
        v_msg_4324_,
        v___y_4325_,
        v___y_4326_,
    );
    lean_dec(v___y_4326_);
    lean_dec_ref(v___y_4325_);
    lean_dec(v_stx_4323_);
    return v_res_4328_;
}
pub unsafe fn l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
    mut v_a_4329_: *mut LeanObject,
    mut v_x_4330_: *mut LeanObject,
) -> u8 {
    let mut v___x_4331_: u8 = 0;
    let mut v_head_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4330_) == 0 {
                    v___x_4331_ = 0;
                    return v___x_4331_;
                } else {
                    v_head_4332_ = lean_ctor_get(v_x_4330_, 0);
                    v_tail_4333_ = lean_ctor_get(v_x_4330_, 1);
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
    mut v_a_4336_: *mut LeanObject,
    mut v_x_4337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4338_: u8 = 0;
    let mut v_r_4339_: *mut LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(v_a_4336_, v_x_4337_);
    lean_dec(v_x_4337_);
    lean_dec_ref(v_a_4336_);
    v_r_4339_ = lean_box((v_res_4338_) as usize);
    return v_r_4339_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    v___x_4341_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__0;
    v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
    return v___x_4342_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
    mut v_as_x27_4343_: *mut LeanObject,
    mut v_b_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4343_) == 0 {
                    v___x_4348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4348_, 0, v_b_4344_);
                    return v___x_4348_;
                } else {
                    v_head_4349_ = lean_ctor_get(v_as_x27_4343_, 0);
                    v_tail_4350_ = lean_ctor_get(v_as_x27_4343_, 1);
                    v_fst_4351_ = lean_ctor_get(v_head_4349_, 0);
                    v_snd_4352_ = lean_ctor_get(v_head_4349_, 1);
                    v___x_4353_ = lean_box(0);
                    if lean_obj_tag(v_snd_4352_) == 1 {
                        v_str_4354_ = lean_ctor_get(v_snd_4352_, 1);
                        v___x_4355_ = l_Lean_Linter_List_allowedWidths;
                        lean_inc_ref(v_str_4354_);
                        v___x_4356_ = l_Lean_Linter_List_stripBinderName(v_str_4354_);
                        v___x_4357_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4356_,
                            v___x_4355_,
                        );
                        lean_dec_ref(v___x_4356_);
                        if v___x_4357_ == 0 {
                            v___x_4358_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4359_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg___closed__1);
                            lean_inc_ref(v_str_4354_);
                            v___x_4360_ = l_Lean_stringToMessageData(v_str_4354_);
                            v___x_4361_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4361_, 0, v___x_4359_);
                            lean_ctor_set(v___x_4361_, 1, v___x_4360_);
                            v___x_4362_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4358_,
                                    v_fst_4351_,
                                    v___x_4361_,
                                    v___y_4345_,
                                    v___y_4346_,
                                );
                            if lean_obj_tag(v___x_4362_) == 0 {
                                lean_dec_ref_known(v___x_4362_, 1);
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
    mut v_as_x27_4366_: *mut LeanObject,
    mut v_b_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4371_: *mut LeanObject = core::ptr::null_mut();
    v_res_4371_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
        v_as_x27_4366_,
        v_b_4367_,
        v___y_4368_,
        v___y_4369_,
    );
    lean_dec(v___y_4369_);
    lean_dec_ref(v___y_4368_);
    lean_dec(v_as_x27_4366_);
    return v_res_4371_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    v___x_4373_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__0;
    v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
    return v___x_4374_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
    mut v_as_x27_4375_: *mut LeanObject,
    mut v_b_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4375_) == 0 {
                    v___x_4380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4380_, 0, v_b_4376_);
                    return v___x_4380_;
                } else {
                    v_head_4381_ = lean_ctor_get(v_as_x27_4375_, 0);
                    v_tail_4382_ = lean_ctor_get(v_as_x27_4375_, 1);
                    v_fst_4383_ = lean_ctor_get(v_head_4381_, 0);
                    v_snd_4384_ = lean_ctor_get(v_head_4381_, 1);
                    v___x_4385_ = lean_box(0);
                    if lean_obj_tag(v_snd_4384_) == 1 {
                        v_str_4386_ = lean_ctor_get(v_snd_4384_, 1);
                        v___x_4387_ = l_Lean_Linter_List_allowedBitVecWidths;
                        lean_inc_ref(v_str_4386_);
                        v___x_4388_ = l_Lean_Linter_List_stripBinderName(v_str_4386_);
                        v___x_4389_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4388_,
                            v___x_4387_,
                        );
                        lean_dec_ref(v___x_4388_);
                        if v___x_4389_ == 0 {
                            v___x_4390_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4391_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg___closed__1);
                            lean_inc_ref(v_str_4386_);
                            v___x_4392_ = l_Lean_stringToMessageData(v_str_4386_);
                            v___x_4393_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4393_, 0, v___x_4391_);
                            lean_ctor_set(v___x_4393_, 1, v___x_4392_);
                            v___x_4394_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4390_,
                                    v_fst_4383_,
                                    v___x_4393_,
                                    v___y_4377_,
                                    v___y_4378_,
                                );
                            if lean_obj_tag(v___x_4394_) == 0 {
                                lean_dec_ref_known(v___x_4394_, 1);
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
    mut v_as_x27_4398_: *mut LeanObject,
    mut v_b_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4403_: *mut LeanObject = core::ptr::null_mut();
    v_res_4403_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
        v_as_x27_4398_,
        v_b_4399_,
        v___y_4400_,
        v___y_4401_,
    );
    lean_dec(v___y_4401_);
    lean_dec_ref(v___y_4400_);
    lean_dec(v_as_x27_4398_);
    return v_res_4403_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    v___x_4405_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__0;
    v___x_4406_ = l_Lean_stringToMessageData(v___x_4405_);
    return v___x_4406_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
    mut v_as_x27_4407_: *mut LeanObject,
    mut v_b_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4407_) == 0 {
                    v___x_4412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4412_, 0, v_b_4408_);
                    return v___x_4412_;
                } else {
                    v_head_4413_ = lean_ctor_get(v_as_x27_4407_, 0);
                    v_tail_4414_ = lean_ctor_get(v_as_x27_4407_, 1);
                    v_fst_4415_ = lean_ctor_get(v_head_4413_, 0);
                    v_snd_4416_ = lean_ctor_get(v_head_4413_, 1);
                    v___x_4417_ = lean_box(0);
                    if lean_obj_tag(v_snd_4416_) == 1 {
                        v_str_4418_ = lean_ctor_get(v_snd_4416_, 1);
                        v___x_4419_ = l_Lean_Linter_List_allowedIndices;
                        lean_inc_ref(v_str_4418_);
                        v___x_4420_ = l_Lean_Linter_List_stripBinderName(v_str_4418_);
                        v___x_4421_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_4420_,
                            v___x_4419_,
                        );
                        lean_dec_ref(v___x_4420_);
                        if v___x_4421_ == 0 {
                            v___x_4422_ = l_Lean_Linter_List_linter_indexVariables;
                            v___x_4423_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg___closed__1);
                            lean_inc_ref(v_str_4418_);
                            v___x_4424_ = l_Lean_stringToMessageData(v_str_4418_);
                            v___x_4425_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4425_, 0, v___x_4423_);
                            lean_ctor_set(v___x_4425_, 1, v___x_4424_);
                            v___x_4426_ =
                                l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                                    v___x_4422_,
                                    v_fst_4415_,
                                    v___x_4425_,
                                    v___y_4409_,
                                    v___y_4410_,
                                );
                            if lean_obj_tag(v___x_4426_) == 0 {
                                lean_dec_ref_known(v___x_4426_, 1);
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
    mut v_as_x27_4430_: *mut LeanObject,
    mut v_b_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4435_: *mut LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
        v_as_x27_4430_,
        v_b_4431_,
        v___y_4432_,
        v___y_4433_,
    );
    lean_dec(v___y_4433_);
    lean_dec_ref(v___y_4432_);
    lean_dec(v_as_x27_4430_);
    return v_res_4435_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(
    mut v_as_4439_: *mut LeanObject,
    mut v_sz_4440_: usize,
    mut v_i_4441_: usize,
    mut v_b_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: usize = 0;
    let mut v___x_4458_: usize = 0;
    let mut v_a_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_a_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4446_ = lean_usize_dec_lt(v_i_4441_, v_sz_4440_);
                if v___x_4446_ == 0 {
                    v___x_4447_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4447_, 0, v_b_4442_);
                    return v___x_4447_;
                } else {
                    lean_dec_ref(v_b_4442_);
                    v___x_4448_ = lean_box(0);
                    v_a_4449_ = lean_array_uget_borrowed(v_as_4439_, v_i_4441_);
                    lean_inc(v_a_4449_);
                    v___x_4450_ = l_Lean_Linter_List_numericalIndices(v_a_4449_);
                    v___x_4451_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4450_, v___x_4448_, v___y_4443_, v___y_4444_);
                    lean_dec(v___x_4450_);
                    if lean_obj_tag(v___x_4451_) == 0 {
                        lean_dec_ref_known(v___x_4451_, 1);
                        lean_inc(v_a_4449_);
                        v___x_4452_ = l_Lean_Linter_List_numericalWidths(v_a_4449_);
                        v___x_4453_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4452_, v___x_4448_, v___y_4443_, v___y_4444_);
                        lean_dec(v___x_4452_);
                        if lean_obj_tag(v___x_4453_) == 0 {
                            lean_dec_ref_known(v___x_4453_, 1);
                            lean_inc(v_a_4449_);
                            v___x_4454_ = l_Lean_Linter_List_bitVecWidths(v_a_4449_);
                            v___x_4455_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4454_, v___x_4448_, v___y_4443_, v___y_4444_);
                            lean_dec(v___x_4454_);
                            if lean_obj_tag(v___x_4455_) == 0 {
                                lean_dec_ref_known(v___x_4455_, 1);
                                v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                v___x_4457_ = 1usize;
                                v___x_4458_ = lean_usize_add(v_i_4441_, v___x_4457_);
                                v_i_4441_ = v___x_4458_;
                                v_b_4442_ = v___x_4456_;
                                state = 0;
                                continue;
                            } else {
                                v_a_4460_ = lean_ctor_get(v___x_4455_, 0);
                                v_isSharedCheck_4467_ = (!lean_is_exclusive(v___x_4455_)) as u8;
                                if v_isSharedCheck_4467_ == 0 {
                                    v___x_4462_ = v___x_4455_;
                                    v_isShared_4463_ = v_isSharedCheck_4467_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4460_);
                                    lean_dec(v___x_4455_);
                                    v___x_4462_ = lean_box(0);
                                    v_isShared_4463_ = v_isSharedCheck_4467_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4468_ = lean_ctor_get(v___x_4453_, 0);
                            v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4453_)) as u8;
                            if v_isSharedCheck_4475_ == 0 {
                                v___x_4470_ = v___x_4453_;
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4468_);
                                lean_dec(v___x_4453_);
                                v___x_4470_ = lean_box(0);
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4476_ = lean_ctor_get(v___x_4451_, 0);
                        v_isSharedCheck_4483_ = (!lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4478_ = v___x_4451_;
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4476_);
                            lean_dec(v___x_4451_);
                            v___x_4478_ = lean_box(0);
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
                    v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
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
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
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
                    v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
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
    mut v_as_4484_: *mut LeanObject,
    mut v_sz_4485_: *mut LeanObject,
    mut v_i_4486_: *mut LeanObject,
    mut v_b_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4491_: usize = 0;
    let mut v_i_boxed_4492_: usize = 0;
    let mut v_res_4493_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4491_ = lean_unbox_usize(v_sz_4485_);
    lean_dec(v_sz_4485_);
    v_i_boxed_4492_ = lean_unbox_usize(v_i_4486_);
    lean_dec(v_i_4486_);
    v_res_4493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_4484_, v_sz_boxed_4491_, v_i_boxed_4492_, v_b_4487_, v___y_4488_, v___y_4489_);
    lean_dec(v___y_4489_);
    lean_dec_ref(v___y_4488_);
    lean_dec_ref(v_as_4484_);
    return v_res_4493_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(
    mut v_as_4494_: *mut LeanObject,
    mut v_sz_4495_: usize,
    mut v_i_4496_: usize,
    mut v_b_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: usize = 0;
    let mut v___x_4513_: usize = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_a_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = lean_usize_dec_lt(v_i_4496_, v_sz_4495_);
                if v___x_4501_ == 0 {
                    v___x_4502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4502_, 0, v_b_4497_);
                    return v___x_4502_;
                } else {
                    lean_dec_ref(v_b_4497_);
                    v___x_4503_ = lean_box(0);
                    v_a_4504_ = lean_array_uget_borrowed(v_as_4494_, v_i_4496_);
                    lean_inc(v_a_4504_);
                    v___x_4505_ = l_Lean_Linter_List_numericalIndices(v_a_4504_);
                    v___x_4506_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4505_, v___x_4503_, v___y_4498_, v___y_4499_);
                    lean_dec(v___x_4505_);
                    if lean_obj_tag(v___x_4506_) == 0 {
                        lean_dec_ref_known(v___x_4506_, 1);
                        lean_inc(v_a_4504_);
                        v___x_4507_ = l_Lean_Linter_List_numericalWidths(v_a_4504_);
                        v___x_4508_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4507_, v___x_4503_, v___y_4498_, v___y_4499_);
                        lean_dec(v___x_4507_);
                        if lean_obj_tag(v___x_4508_) == 0 {
                            lean_dec_ref_known(v___x_4508_, 1);
                            lean_inc(v_a_4504_);
                            v___x_4509_ = l_Lean_Linter_List_bitVecWidths(v_a_4504_);
                            v___x_4510_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4509_, v___x_4503_, v___y_4498_, v___y_4499_);
                            lean_dec(v___x_4509_);
                            if lean_obj_tag(v___x_4510_) == 0 {
                                lean_dec_ref_known(v___x_4510_, 1);
                                v___x_4511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                v___x_4512_ = 1usize;
                                v___x_4513_ = lean_usize_add(v_i_4496_, v___x_4512_);
                                v___x_4514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13(v_as_4494_, v_sz_4495_, v___x_4513_, v___x_4511_, v___y_4498_, v___y_4499_);
                                return v___x_4514_;
                            } else {
                                v_a_4515_ = lean_ctor_get(v___x_4510_, 0);
                                v_isSharedCheck_4522_ = (!lean_is_exclusive(v___x_4510_)) as u8;
                                if v_isSharedCheck_4522_ == 0 {
                                    v___x_4517_ = v___x_4510_;
                                    v_isShared_4518_ = v_isSharedCheck_4522_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4515_);
                                    lean_dec(v___x_4510_);
                                    v___x_4517_ = lean_box(0);
                                    v_isShared_4518_ = v_isSharedCheck_4522_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4523_ = lean_ctor_get(v___x_4508_, 0);
                            v_isSharedCheck_4530_ = (!lean_is_exclusive(v___x_4508_)) as u8;
                            if v_isSharedCheck_4530_ == 0 {
                                v___x_4525_ = v___x_4508_;
                                v_isShared_4526_ = v_isSharedCheck_4530_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4523_);
                                lean_dec(v___x_4508_);
                                v___x_4525_ = lean_box(0);
                                v_isShared_4526_ = v_isSharedCheck_4530_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4531_ = lean_ctor_get(v___x_4506_, 0);
                        v_isSharedCheck_4538_ = (!lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4538_ == 0 {
                            v___x_4533_ = v___x_4506_;
                            v_isShared_4534_ = v_isSharedCheck_4538_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4531_);
                            lean_dec(v___x_4506_);
                            v___x_4533_ = lean_box(0);
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
                    v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
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
                    v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
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
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
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
    mut v_as_4539_: *mut LeanObject,
    mut v_sz_4540_: *mut LeanObject,
    mut v_i_4541_: *mut LeanObject,
    mut v_b_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4546_: usize = 0;
    let mut v_i_boxed_4547_: usize = 0;
    let mut v_res_4548_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4546_ = lean_unbox_usize(v_sz_4540_);
    lean_dec(v_sz_4540_);
    v_i_boxed_4547_ = lean_unbox_usize(v_i_4541_);
    lean_dec(v_i_4541_);
    v_res_4548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_as_4539_, v_sz_boxed_4546_, v_i_boxed_4547_, v_b_4542_, v___y_4543_, v___y_4544_);
    lean_dec(v___y_4544_);
    lean_dec_ref(v___y_4543_);
    lean_dec_ref(v_as_4539_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(
    mut v_init_4549_: *mut LeanObject,
    mut v_n_4550_: *mut LeanObject,
    mut v_b_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v_fst_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_a_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4583_: u8 = 0;
    let mut v_vs_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4587_: usize = 0;
    let mut v___x_4588_: usize = 0;
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_fst_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_a_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_4550_) == 0 {
                    v_cs_4555_ = lean_ctor_get(v_n_4550_, 0);
                    v___x_4556_ = lean_box(0);
                    v___x_4557_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4557_, 0, v___x_4556_);
                    lean_ctor_set(v___x_4557_, 1, v_b_4551_);
                    v_sz_4558_ = lean_array_size(v_cs_4555_);
                    v___x_4559_ = 0usize;
                    v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_4549_, v_cs_4555_, v_sz_4558_, v___x_4559_, v___x_4557_, v___y_4552_, v___y_4553_);
                    if lean_obj_tag(v___x_4560_) == 0 {
                        v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
                        v_isSharedCheck_4575_ = (!lean_is_exclusive(v___x_4560_)) as u8;
                        if v_isSharedCheck_4575_ == 0 {
                            v___x_4563_ = v___x_4560_;
                            v_isShared_4564_ = v_isSharedCheck_4575_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4561_);
                            lean_dec(v___x_4560_);
                            v___x_4563_ = lean_box(0);
                            v_isShared_4564_ = v_isSharedCheck_4575_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4576_ = lean_ctor_get(v___x_4560_, 0);
                        v_isSharedCheck_4583_ = (!lean_is_exclusive(v___x_4560_)) as u8;
                        if v_isSharedCheck_4583_ == 0 {
                            v___x_4578_ = v___x_4560_;
                            v_isShared_4579_ = v_isSharedCheck_4583_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4576_);
                            lean_dec(v___x_4560_);
                            v___x_4578_ = lean_box(0);
                            v_isShared_4579_ = v_isSharedCheck_4583_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4584_ = lean_ctor_get(v_n_4550_, 0);
                    v___x_4585_ = lean_box(0);
                    v___x_4586_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4586_, 0, v___x_4585_);
                    lean_ctor_set(v___x_4586_, 1, v_b_4551_);
                    v_sz_4587_ = lean_array_size(v_vs_4584_);
                    v___x_4588_ = 0usize;
                    v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10(v_vs_4584_, v_sz_4587_, v___x_4588_, v___x_4586_, v___y_4552_, v___y_4553_);
                    if lean_obj_tag(v___x_4589_) == 0 {
                        v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
                        v_isSharedCheck_4604_ = (!lean_is_exclusive(v___x_4589_)) as u8;
                        if v_isSharedCheck_4604_ == 0 {
                            v___x_4592_ = v___x_4589_;
                            v_isShared_4593_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4590_);
                            lean_dec(v___x_4589_);
                            v___x_4592_ = lean_box(0);
                            v_isShared_4593_ = v_isSharedCheck_4604_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4605_ = lean_ctor_get(v___x_4589_, 0);
                        v_isSharedCheck_4612_ = (!lean_is_exclusive(v___x_4589_)) as u8;
                        if v_isSharedCheck_4612_ == 0 {
                            v___x_4607_ = v___x_4589_;
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4605_);
                            lean_dec(v___x_4589_);
                            v___x_4607_ = lean_box(0);
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4565_ = lean_ctor_get(v_a_4561_, 0);
                if lean_obj_tag(v_fst_4565_) == 0 {
                    v_snd_4566_ = lean_ctor_get(v_a_4561_, 1);
                    lean_inc(v_snd_4566_);
                    lean_dec(v_a_4561_);
                    v___x_4567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4567_, 0, v_snd_4566_);
                    if v_isShared_4564_ == 0 {
                        lean_ctor_set(v___x_4563_, 0, v___x_4567_);
                        v___x_4569_ = v___x_4563_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                        v___x_4569_ = v_reuseFailAlloc_4570_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4565_);
                    lean_dec(v_a_4561_);
                    v_val_4571_ = lean_ctor_get(v_fst_4565_, 0);
                    lean_inc(v_val_4571_);
                    lean_dec_ref_known(v_fst_4565_, 1);
                    if v_isShared_4564_ == 0 {
                        lean_ctor_set(v___x_4563_, 0, v_val_4571_);
                        v___x_4573_ = v___x_4563_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_val_4571_);
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
                    v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
                    v___x_4581_ = v_reuseFailAlloc_4582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4581_;
            }
            6 => {
                v_fst_4594_ = lean_ctor_get(v_a_4590_, 0);
                if lean_obj_tag(v_fst_4594_) == 0 {
                    v_snd_4595_ = lean_ctor_get(v_a_4590_, 1);
                    lean_inc(v_snd_4595_);
                    lean_dec(v_a_4590_);
                    v___x_4596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4596_, 0, v_snd_4595_);
                    if v_isShared_4593_ == 0 {
                        lean_ctor_set(v___x_4592_, 0, v___x_4596_);
                        v___x_4598_ = v___x_4592_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
                        v___x_4598_ = v_reuseFailAlloc_4599_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4594_);
                    lean_dec(v_a_4590_);
                    v_val_4600_ = lean_ctor_get(v_fst_4594_, 0);
                    lean_inc(v_val_4600_);
                    lean_dec_ref_known(v_fst_4594_, 1);
                    if v_isShared_4593_ == 0 {
                        lean_ctor_set(v___x_4592_, 0, v_val_4600_);
                        v___x_4602_ = v___x_4592_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_val_4600_);
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
                    v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
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
    mut v_init_4613_: *mut LeanObject,
    mut v_as_4614_: *mut LeanObject,
    mut v_sz_4615_: usize,
    mut v_i_4616_: usize,
    mut v_b_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v_a_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4632_: u8 = 0;
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: usize = 0;
    let mut v___x_4645_: usize = 0;
    let mut v_reuseFailAlloc_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v_a_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_unused_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4621_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
                if v___x_4621_ == 0 {
                    v___x_4622_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4622_, 0, v_b_4617_);
                    return v___x_4622_;
                } else {
                    v_snd_4623_ = lean_ctor_get(v_b_4617_, 1);
                    v_isSharedCheck_4657_ = (!lean_is_exclusive(v_b_4617_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v_unused_4658_ = lean_ctor_get(v_b_4617_, 0);
                        lean_dec(v_unused_4658_);
                        v___x_4625_ = v_b_4617_;
                        v_isShared_4626_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4623_);
                        lean_dec(v_b_4617_);
                        v___x_4625_ = lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4627_ = lean_array_uget_borrowed(v_as_4614_, v_i_4616_);
                lean_inc(v_snd_4623_);
                v___x_4628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4613_, v_a_4627_, v_snd_4623_, v___y_4618_, v___y_4619_);
                if lean_obj_tag(v___x_4628_) == 0 {
                    v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
                    v_isSharedCheck_4648_ = (!lean_is_exclusive(v___x_4628_)) as u8;
                    if v_isSharedCheck_4648_ == 0 {
                        v___x_4631_ = v___x_4628_;
                        v_isShared_4632_ = v_isSharedCheck_4648_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4629_);
                        lean_dec(v___x_4628_);
                        v___x_4631_ = lean_box(0);
                        v_isShared_4632_ = v_isSharedCheck_4648_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4625_);
                    lean_dec(v_snd_4623_);
                    v_a_4649_ = lean_ctor_get(v___x_4628_, 0);
                    v_isSharedCheck_4656_ = (!lean_is_exclusive(v___x_4628_)) as u8;
                    if v_isSharedCheck_4656_ == 0 {
                        v___x_4651_ = v___x_4628_;
                        v_isShared_4652_ = v_isSharedCheck_4656_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4649_);
                        lean_dec(v___x_4628_);
                        v___x_4651_ = lean_box(0);
                        v_isShared_4652_ = v_isSharedCheck_4656_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4629_) == 0 {
                    v___x_4633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4633_, 0, v_a_4629_);
                    if v_isShared_4626_ == 0 {
                        lean_ctor_set(v___x_4625_, 0, v___x_4633_);
                        v___x_4635_ = v___x_4625_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4633_);
                        lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_snd_4623_);
                        v___x_4635_ = v_reuseFailAlloc_4639_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4631_);
                    lean_dec(v_snd_4623_);
                    v_a_4640_ = lean_ctor_get(v_a_4629_, 0);
                    lean_inc(v_a_4640_);
                    lean_dec_ref_known(v_a_4629_, 1);
                    v___x_4641_ = lean_box(0);
                    if v_isShared_4626_ == 0 {
                        lean_ctor_set(v___x_4625_, 1, v_a_4640_);
                        lean_ctor_set(v___x_4625_, 0, v___x_4641_);
                        v___x_4643_ = v___x_4625_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4641_);
                        lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_a_4640_);
                        v___x_4643_ = v_reuseFailAlloc_4647_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4632_ == 0 {
                    lean_ctor_set(v___x_4631_, 0, v___x_4635_);
                    v___x_4637_ = v___x_4631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
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
                    v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
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
    mut v_init_4659_: *mut LeanObject,
    mut v_as_4660_: *mut LeanObject,
    mut v_sz_4661_: *mut LeanObject,
    mut v_i_4662_: *mut LeanObject,
    mut v_b_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4667_: usize = 0;
    let mut v_i_boxed_4668_: usize = 0;
    let mut v_res_4669_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4667_ = lean_unbox_usize(v_sz_4661_);
    lean_dec(v_sz_4661_);
    v_i_boxed_4668_ = lean_unbox_usize(v_i_4662_);
    lean_dec(v_i_4662_);
    v_res_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__9(v_init_4659_, v_as_4660_, v_sz_boxed_4667_, v_i_boxed_4668_, v_b_4663_, v___y_4664_, v___y_4665_);
    lean_dec(v___y_4665_);
    lean_dec_ref(v___y_4664_);
    lean_dec_ref(v_as_4660_);
    return v_res_4669_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7___boxed(
    mut v_init_4670_: *mut LeanObject,
    mut v_n_4671_: *mut LeanObject,
    mut v_b_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4676_: *mut LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4670_, v_n_4671_, v_b_4672_, v___y_4673_, v___y_4674_);
    lean_dec(v___y_4674_);
    lean_dec_ref(v___y_4673_);
    lean_dec_ref(v_n_4671_);
    return v_res_4676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(
    mut v_as_4680_: *mut LeanObject,
    mut v_sz_4681_: usize,
    mut v_i_4682_: usize,
    mut v_b_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: usize = 0;
    let mut v___x_4699_: usize = 0;
    let mut v_a_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut v_a_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4716_: u8 = 0;
    let mut v_a_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4687_ = lean_usize_dec_lt(v_i_4682_, v_sz_4681_);
                if v___x_4687_ == 0 {
                    v___x_4688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4688_, 0, v_b_4683_);
                    return v___x_4688_;
                } else {
                    lean_dec_ref(v_b_4683_);
                    v___x_4689_ = lean_box(0);
                    v_a_4690_ = lean_array_uget_borrowed(v_as_4680_, v_i_4682_);
                    lean_inc(v_a_4690_);
                    v___x_4691_ = l_Lean_Linter_List_numericalIndices(v_a_4690_);
                    v___x_4692_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4691_, v___x_4689_, v___y_4684_, v___y_4685_);
                    lean_dec(v___x_4691_);
                    if lean_obj_tag(v___x_4692_) == 0 {
                        lean_dec_ref_known(v___x_4692_, 1);
                        lean_inc(v_a_4690_);
                        v___x_4693_ = l_Lean_Linter_List_numericalWidths(v_a_4690_);
                        v___x_4694_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4693_, v___x_4689_, v___y_4684_, v___y_4685_);
                        lean_dec(v___x_4693_);
                        if lean_obj_tag(v___x_4694_) == 0 {
                            lean_dec_ref_known(v___x_4694_, 1);
                            lean_inc(v_a_4690_);
                            v___x_4695_ = l_Lean_Linter_List_bitVecWidths(v_a_4690_);
                            v___x_4696_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4695_, v___x_4689_, v___y_4684_, v___y_4685_);
                            lean_dec(v___x_4695_);
                            if lean_obj_tag(v___x_4696_) == 0 {
                                lean_dec_ref_known(v___x_4696_, 1);
                                v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                v___x_4698_ = 1usize;
                                v___x_4699_ = lean_usize_add(v_i_4682_, v___x_4698_);
                                v_i_4682_ = v___x_4699_;
                                v_b_4683_ = v___x_4697_;
                                state = 0;
                                continue;
                            } else {
                                v_a_4701_ = lean_ctor_get(v___x_4696_, 0);
                                v_isSharedCheck_4708_ = (!lean_is_exclusive(v___x_4696_)) as u8;
                                if v_isSharedCheck_4708_ == 0 {
                                    v___x_4703_ = v___x_4696_;
                                    v_isShared_4704_ = v_isSharedCheck_4708_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4701_);
                                    lean_dec(v___x_4696_);
                                    v___x_4703_ = lean_box(0);
                                    v_isShared_4704_ = v_isSharedCheck_4708_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4709_ = lean_ctor_get(v___x_4694_, 0);
                            v_isSharedCheck_4716_ = (!lean_is_exclusive(v___x_4694_)) as u8;
                            if v_isSharedCheck_4716_ == 0 {
                                v___x_4711_ = v___x_4694_;
                                v_isShared_4712_ = v_isSharedCheck_4716_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4709_);
                                lean_dec(v___x_4694_);
                                v___x_4711_ = lean_box(0);
                                v_isShared_4712_ = v_isSharedCheck_4716_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4717_ = lean_ctor_get(v___x_4692_, 0);
                        v_isSharedCheck_4724_ = (!lean_is_exclusive(v___x_4692_)) as u8;
                        if v_isSharedCheck_4724_ == 0 {
                            v___x_4719_ = v___x_4692_;
                            v_isShared_4720_ = v_isSharedCheck_4724_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4717_);
                            lean_dec(v___x_4692_);
                            v___x_4719_ = lean_box(0);
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
                    v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
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
                    v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
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
                    v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
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
    mut v_as_4725_: *mut LeanObject,
    mut v_sz_4726_: *mut LeanObject,
    mut v_i_4727_: *mut LeanObject,
    mut v_b_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4732_: usize = 0;
    let mut v_i_boxed_4733_: usize = 0;
    let mut v_res_4734_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4732_ = lean_unbox_usize(v_sz_4726_);
    lean_dec(v_sz_4726_);
    v_i_boxed_4733_ = lean_unbox_usize(v_i_4727_);
    lean_dec(v_i_4727_);
    v_res_4734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_4725_, v_sz_boxed_4732_, v_i_boxed_4733_, v_b_4728_, v___y_4729_, v___y_4730_);
    lean_dec(v___y_4730_);
    lean_dec_ref(v___y_4729_);
    lean_dec_ref(v_as_4725_);
    return v_res_4734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(
    mut v_as_4735_: *mut LeanObject,
    mut v_sz_4736_: usize,
    mut v_i_4737_: usize,
    mut v_b_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4742_: u8 = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_a_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut v_a_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4775_: u8 = 0;
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = lean_usize_dec_lt(v_i_4737_, v_sz_4736_);
                if v___x_4742_ == 0 {
                    v___x_4743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4743_, 0, v_b_4738_);
                    return v___x_4743_;
                } else {
                    lean_dec_ref(v_b_4738_);
                    v___x_4744_ = lean_box(0);
                    v_a_4745_ = lean_array_uget_borrowed(v_as_4735_, v_i_4737_);
                    lean_inc(v_a_4745_);
                    v___x_4746_ = l_Lean_Linter_List_numericalIndices(v_a_4745_);
                    v___x_4747_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(v___x_4746_, v___x_4744_, v___y_4739_, v___y_4740_);
                    lean_dec(v___x_4746_);
                    if lean_obj_tag(v___x_4747_) == 0 {
                        lean_dec_ref_known(v___x_4747_, 1);
                        lean_inc(v_a_4745_);
                        v___x_4748_ = l_Lean_Linter_List_numericalWidths(v_a_4745_);
                        v___x_4749_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(v___x_4748_, v___x_4744_, v___y_4739_, v___y_4740_);
                        lean_dec(v___x_4748_);
                        if lean_obj_tag(v___x_4749_) == 0 {
                            lean_dec_ref_known(v___x_4749_, 1);
                            lean_inc(v_a_4745_);
                            v___x_4750_ = l_Lean_Linter_List_bitVecWidths(v_a_4745_);
                            v___x_4751_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(v___x_4750_, v___x_4744_, v___y_4739_, v___y_4740_);
                            lean_dec(v___x_4750_);
                            if lean_obj_tag(v___x_4751_) == 0 {
                                lean_dec_ref_known(v___x_4751_, 1);
                                v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                v___x_4753_ = 1usize;
                                v___x_4754_ = lean_usize_add(v_i_4737_, v___x_4753_);
                                v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12(v_as_4735_, v_sz_4736_, v___x_4754_, v___x_4752_, v___y_4739_, v___y_4740_);
                                return v___x_4755_;
                            } else {
                                v_a_4756_ = lean_ctor_get(v___x_4751_, 0);
                                v_isSharedCheck_4763_ = (!lean_is_exclusive(v___x_4751_)) as u8;
                                if v_isSharedCheck_4763_ == 0 {
                                    v___x_4758_ = v___x_4751_;
                                    v_isShared_4759_ = v_isSharedCheck_4763_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4756_);
                                    lean_dec(v___x_4751_);
                                    v___x_4758_ = lean_box(0);
                                    v_isShared_4759_ = v_isSharedCheck_4763_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4764_ = lean_ctor_get(v___x_4749_, 0);
                            v_isSharedCheck_4771_ = (!lean_is_exclusive(v___x_4749_)) as u8;
                            if v_isSharedCheck_4771_ == 0 {
                                v___x_4766_ = v___x_4749_;
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4764_);
                                lean_dec(v___x_4749_);
                                v___x_4766_ = lean_box(0);
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4772_ = lean_ctor_get(v___x_4747_, 0);
                        v_isSharedCheck_4779_ = (!lean_is_exclusive(v___x_4747_)) as u8;
                        if v_isSharedCheck_4779_ == 0 {
                            v___x_4774_ = v___x_4747_;
                            v_isShared_4775_ = v_isSharedCheck_4779_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4772_);
                            lean_dec(v___x_4747_);
                            v___x_4774_ = lean_box(0);
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
                    v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
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
                    v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
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
                    v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
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
    mut v_as_4780_: *mut LeanObject,
    mut v_sz_4781_: *mut LeanObject,
    mut v_i_4782_: *mut LeanObject,
    mut v_b_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4787_: usize = 0;
    let mut v_i_boxed_4788_: usize = 0;
    let mut v_res_4789_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4787_ = lean_unbox_usize(v_sz_4781_);
    lean_dec(v_sz_4781_);
    v_i_boxed_4788_ = lean_unbox_usize(v_i_4782_);
    lean_dec(v_i_4782_);
    v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_as_4780_, v_sz_boxed_4787_, v_i_boxed_4788_, v_b_4783_, v___y_4784_, v___y_4785_);
    lean_dec(v___y_4785_);
    lean_dec_ref(v___y_4784_);
    lean_dec_ref(v_as_4780_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(
    mut v_t_4790_: *mut LeanObject,
    mut v_init_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4809_: usize = 0;
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4815_: u8 = 0;
    let mut v_fst_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4795_ = lean_ctor_get(v_t_4790_, 0);
                v_tail_4796_ = lean_ctor_get(v_t_4790_, 1);
                v___x_4797_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7(v_init_4791_, v_root_4795_, v_init_4791_, v___y_4792_, v___y_4793_);
                if lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4834_ = (!lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4834_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4798_);
                        lean_dec(v___x_4797_);
                        v___x_4800_ = lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4835_ = lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4842_ = (!lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4837_ = v___x_4797_;
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4835_);
                        lean_dec(v___x_4797_);
                        v___x_4837_ = lean_box(0);
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4798_) == 0 {
                    v_a_4802_ = lean_ctor_get(v_a_4798_, 0);
                    lean_inc(v_a_4802_);
                    lean_dec_ref_known(v_a_4798_, 1);
                    if v_isShared_4801_ == 0 {
                        lean_ctor_set(v___x_4800_, 0, v_a_4802_);
                        v___x_4804_ = v___x_4800_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4802_);
                        v___x_4804_ = v_reuseFailAlloc_4805_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4800_);
                    v_a_4806_ = lean_ctor_get(v_a_4798_, 0);
                    lean_inc(v_a_4806_);
                    lean_dec_ref_known(v_a_4798_, 1);
                    v___x_4807_ = lean_box(0);
                    v___x_4808_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4808_, 0, v___x_4807_);
                    lean_ctor_set(v___x_4808_, 1, v_a_4806_);
                    v_sz_4809_ = lean_array_size(v_tail_4796_);
                    v___x_4810_ = 0usize;
                    v___x_4811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8(v_tail_4796_, v_sz_4809_, v___x_4810_, v___x_4808_, v___y_4792_, v___y_4793_);
                    if lean_obj_tag(v___x_4811_) == 0 {
                        v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
                        v_isSharedCheck_4825_ = (!lean_is_exclusive(v___x_4811_)) as u8;
                        if v_isSharedCheck_4825_ == 0 {
                            v___x_4814_ = v___x_4811_;
                            v_isShared_4815_ = v_isSharedCheck_4825_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4812_);
                            lean_dec(v___x_4811_);
                            v___x_4814_ = lean_box(0);
                            v_isShared_4815_ = v_isSharedCheck_4825_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4826_ = lean_ctor_get(v___x_4811_, 0);
                        v_isSharedCheck_4833_ = (!lean_is_exclusive(v___x_4811_)) as u8;
                        if v_isSharedCheck_4833_ == 0 {
                            v___x_4828_ = v___x_4811_;
                            v_isShared_4829_ = v_isSharedCheck_4833_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4826_);
                            lean_dec(v___x_4811_);
                            v___x_4828_ = lean_box(0);
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
                v_fst_4816_ = lean_ctor_get(v_a_4812_, 0);
                if lean_obj_tag(v_fst_4816_) == 0 {
                    v_snd_4817_ = lean_ctor_get(v_a_4812_, 1);
                    lean_inc(v_snd_4817_);
                    lean_dec(v_a_4812_);
                    if v_isShared_4815_ == 0 {
                        lean_ctor_set(v___x_4814_, 0, v_snd_4817_);
                        v___x_4819_ = v___x_4814_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_snd_4817_);
                        v___x_4819_ = v_reuseFailAlloc_4820_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4816_);
                    lean_dec(v_a_4812_);
                    v_val_4821_ = lean_ctor_get(v_fst_4816_, 0);
                    lean_inc(v_val_4821_);
                    lean_dec_ref_known(v_fst_4816_, 1);
                    if v_isShared_4815_ == 0 {
                        lean_ctor_set(v___x_4814_, 0, v_val_4821_);
                        v___x_4823_ = v___x_4814_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_val_4821_);
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
                    v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
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
                    v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
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
    mut v_t_4843_: *mut LeanObject,
    mut v_init_4844_: *mut LeanObject,
    mut v___y_4845_: *mut LeanObject,
    mut v___y_4846_: *mut LeanObject,
    mut v___y_4847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4848_: *mut LeanObject = core::ptr::null_mut();
    v_res_4848_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(
        v_t_4843_,
        v_init_4844_,
        v___y_4845_,
        v___y_4846_,
    );
    lean_dec(v___y_4846_);
    lean_dec_ref(v___y_4845_);
    lean_dec_ref(v_t_4843_);
    return v_res_4848_;
}
pub unsafe fn l_Lean_Linter_List_indexLinter___lam__0(
    mut v_stx_4849_: *mut LeanObject,
    mut v___y_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v_v_4869_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_4880_: u8 = 0;
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4891_: u8 = 0;
    let mut v_unused_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4853_ = lean_st_ref_get(v___y_4851_);
                v_scopes_4857_ = lean_ctor_get(v___x_4853_, 2);
                lean_inc(v_scopes_4857_);
                lean_dec(v___x_4853_);
                v___x_4858_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_4859_ = l_List_head_x21___redArg(v___x_4858_, v_scopes_4857_);
                lean_dec(v_scopes_4857_);
                v_opts_4860_ = lean_ctor_get(v___x_4859_, 1);
                lean_inc_ref(v_opts_4860_);
                lean_dec(v___x_4859_);
                v___x_4861_ = l_Lean_Linter_List_linter_indexVariables;
                v_name_4862_ = lean_ctor_get(v___x_4861_, 0);
                v_map_4863_ = lean_ctor_get(v_opts_4860_, 0);
                lean_inc(v_map_4863_);
                lean_dec_ref(v_opts_4860_);
                v___x_4864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4863_, v_name_4862_);
                lean_dec(v_map_4863_);
                if lean_obj_tag(v___x_4864_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4865_ = lean_ctor_get(v___x_4864_, 0);
                    v_isSharedCheck_4897_ = (!lean_is_exclusive(v___x_4864_)) as u8;
                    if v_isSharedCheck_4897_ == 0 {
                        v___x_4867_ = v___x_4864_;
                        v_isShared_4868_ = v_isSharedCheck_4897_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4865_);
                        lean_dec(v___x_4864_);
                        v___x_4867_ = lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4897_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4855_ = lean_box(0);
                v___x_4856_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4856_, 0, v___x_4855_);
                return v___x_4856_;
            }
            2 => {
                if lean_obj_tag(v_val_4865_) == 1 {
                    v_v_4869_ = lean_ctor_get_uint8(v_val_4865_, 0 as u32);
                    lean_dec_ref_known(v_val_4865_, 0);
                    if v_v_4869_ == 0 {
                        lean_del_object(v___x_4867_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4870_ = lean_st_ref_get(v___y_4851_);
                        v_messages_4871_ = lean_ctor_get(v___x_4870_, 1);
                        lean_inc_ref(v_messages_4871_);
                        lean_dec(v___x_4870_);
                        v___x_4872_ = l_Lean_MessageLog_hasErrors(v_messages_4871_);
                        lean_dec_ref(v_messages_4871_);
                        if v___x_4872_ == 0 {
                            v___x_4873_ = lean_st_ref_get(v___y_4851_);
                            v_infoState_4879_ = lean_ctor_get(v___x_4873_, 8);
                            lean_inc_ref(v_infoState_4879_);
                            lean_dec(v___x_4873_);
                            v_enabled_4880_ = lean_ctor_get_uint8(
                                v_infoState_4879_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            lean_dec_ref(v_infoState_4879_);
                            if v_enabled_4880_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_4872_ == 0 {
                                    lean_del_object(v___x_4867_);
                                    v___x_4881_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_4851_);
                                    v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
                                    lean_inc(v_a_4882_);
                                    lean_dec_ref(v___x_4881_);
                                    v___x_4883_ = lean_box(0);
                                    v___x_4884_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6(v_a_4882_, v___x_4883_, v___y_4850_, v___y_4851_);
                                    lean_dec(v_a_4882_);
                                    if lean_obj_tag(v___x_4884_) == 0 {
                                        v_isSharedCheck_4891_ =
                                            (!lean_is_exclusive(v___x_4884_)) as u8;
                                        if v_isSharedCheck_4891_ == 0 {
                                            v_unused_4892_ = lean_ctor_get(v___x_4884_, 0);
                                            lean_dec(v_unused_4892_);
                                            v___x_4886_ = v___x_4884_;
                                            v_isShared_4887_ = v_isSharedCheck_4891_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_dec(v___x_4884_);
                                            v___x_4886_ = lean_box(0);
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
                            v___x_4893_ = lean_box(0);
                            if v_isShared_4868_ == 0 {
                                lean_ctor_set_tag(v___x_4867_, 0);
                                lean_ctor_set(v___x_4867_, 0, v___x_4893_);
                                v___x_4895_ = v___x_4867_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
                                v___x_4895_ = v_reuseFailAlloc_4896_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4867_);
                    lean_dec(v_val_4865_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4875_ = lean_box(0);
                if v_isShared_4868_ == 0 {
                    lean_ctor_set_tag(v___x_4867_, 0);
                    lean_ctor_set(v___x_4867_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4867_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
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
                    lean_ctor_set(v___x_4886_, 0, v___x_4883_);
                    v___x_4889_ = v___x_4886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4883_);
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
    mut v_stx_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4902_: *mut LeanObject = core::ptr::null_mut();
    v_res_4902_ = l_Lean_Linter_List_indexLinter___lam__0(v_stx_4898_, v___y_4899_, v___y_4900_);
    lean_dec(v___y_4900_);
    lean_dec_ref(v___y_4899_);
    lean_dec(v_stx_4898_);
    return v_res_4902_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(
    mut v_as_4916_: *mut LeanObject,
    mut v_as_x27_4917_: *mut LeanObject,
    mut v_b_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
    mut v___y_4921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    v___x_4923_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___redArg(
        v_as_x27_4917_,
        v_b_4918_,
        v___y_4920_,
        v___y_4921_,
    );
    return v___x_4923_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3___boxed(
    mut v_as_4924_: *mut LeanObject,
    mut v_as_x27_4925_: *mut LeanObject,
    mut v_b_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4931_: *mut LeanObject = core::ptr::null_mut();
    v_res_4931_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__3(
        v_as_4924_,
        v_as_x27_4925_,
        v_b_4926_,
        v_a_4927_,
        v___y_4928_,
        v___y_4929_,
    );
    lean_dec(v___y_4929_);
    lean_dec_ref(v___y_4928_);
    lean_dec(v_as_x27_4925_);
    lean_dec(v_as_4924_);
    return v_res_4931_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(
    mut v_as_4932_: *mut LeanObject,
    mut v_as_x27_4933_: *mut LeanObject,
    mut v_b_4934_: *mut LeanObject,
    mut v_a_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___redArg(
        v_as_x27_4933_,
        v_b_4934_,
        v___y_4936_,
        v___y_4937_,
    );
    return v___x_4939_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4___boxed(
    mut v_as_4940_: *mut LeanObject,
    mut v_as_x27_4941_: *mut LeanObject,
    mut v_b_4942_: *mut LeanObject,
    mut v_a_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
    mut v___y_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4947_: *mut LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__4(
        v_as_4940_,
        v_as_x27_4941_,
        v_b_4942_,
        v_a_4943_,
        v___y_4944_,
        v___y_4945_,
    );
    lean_dec(v___y_4945_);
    lean_dec_ref(v___y_4944_);
    lean_dec(v_as_x27_4941_);
    lean_dec(v_as_4940_);
    return v_res_4947_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(
    mut v_as_4948_: *mut LeanObject,
    mut v_as_x27_4949_: *mut LeanObject,
    mut v_b_4950_: *mut LeanObject,
    mut v_a_4951_: *mut LeanObject,
    mut v___y_4952_: *mut LeanObject,
    mut v___y_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    v___x_4955_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___redArg(
        v_as_x27_4949_,
        v_b_4950_,
        v___y_4952_,
        v___y_4953_,
    );
    return v___x_4955_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5___boxed(
    mut v_as_4956_: *mut LeanObject,
    mut v_as_x27_4957_: *mut LeanObject,
    mut v_b_4958_: *mut LeanObject,
    mut v_a_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4963_: *mut LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_indexLinter_spec__5(
        v_as_4956_,
        v_as_x27_4957_,
        v_b_4958_,
        v_a_4959_,
        v___y_4960_,
        v___y_4961_,
    );
    lean_dec(v___y_4961_);
    lean_dec_ref(v___y_4960_);
    lean_dec(v_as_x27_4957_);
    lean_dec(v_as_4956_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(
    mut v_msgData_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    v___x_4968_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___redArg(v_msgData_4964_, v___y_4966_);
    return v___x_4968_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8___boxed(
    mut v_msgData_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4973_: *mut LeanObject = core::ptr::null_mut();
    v_res_4973_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2_spec__2_spec__3_spec__8(v_msgData_4969_, v___y_4970_, v___y_4971_);
    lean_dec(v___y_4971_);
    lean_dec_ref(v___y_4970_);
    return v_res_4973_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    v___x_4975_ = l_Lean_Linter_List_indexLinter;
    v___x_4976_ = l_Lean_Elab_Command_addLinter(v___x_4975_);
    return v___x_4976_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2____boxed(
    mut v_a_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4978_: *mut LeanObject = core::ptr::null_mut();
    v_res_4978_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
    return v_res_4978_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
    mut v_e_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5040_: u8 = 0;
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_unused_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5040_ = l_Lean_Expr_hasMVar(v_e_5037_);
                if v___x_5040_ == 0 {
                    v___x_5041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5041_, 0, v_e_5037_);
                    return v___x_5041_;
                } else {
                    v___x_5042_ = lean_st_ref_get(v___y_5038_);
                    v_mctx_5043_ = lean_ctor_get(v___x_5042_, 0);
                    lean_inc_ref(v_mctx_5043_);
                    lean_dec(v___x_5042_);
                    v___x_5044_ = l_Lean_instantiateMVarsCore(v_mctx_5043_, v_e_5037_);
                    v_fst_5045_ = lean_ctor_get(v___x_5044_, 0);
                    lean_inc(v_fst_5045_);
                    v_snd_5046_ = lean_ctor_get(v___x_5044_, 1);
                    lean_inc(v_snd_5046_);
                    lean_dec_ref(v___x_5044_);
                    v___x_5047_ = lean_st_ref_take(v___y_5038_);
                    v_cache_5048_ = lean_ctor_get(v___x_5047_, 1);
                    v_zetaDeltaFVarIds_5049_ = lean_ctor_get(v___x_5047_, 2);
                    v_postponed_5050_ = lean_ctor_get(v___x_5047_, 3);
                    v_diag_5051_ = lean_ctor_get(v___x_5047_, 4);
                    v_isSharedCheck_5060_ = (!lean_is_exclusive(v___x_5047_)) as u8;
                    if v_isSharedCheck_5060_ == 0 {
                        v_unused_5061_ = lean_ctor_get(v___x_5047_, 0);
                        lean_dec(v_unused_5061_);
                        v___x_5053_ = v___x_5047_;
                        v_isShared_5054_ = v_isSharedCheck_5060_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5051_);
                        lean_inc(v_postponed_5050_);
                        lean_inc(v_zetaDeltaFVarIds_5049_);
                        lean_inc(v_cache_5048_);
                        lean_dec(v___x_5047_);
                        v___x_5053_ = lean_box(0);
                        v_isShared_5054_ = v_isSharedCheck_5060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5054_ == 0 {
                    lean_ctor_set(v___x_5053_, 0, v_snd_5046_);
                    v___x_5056_ = v___x_5053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_snd_5046_);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_cache_5048_);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 2, v_zetaDeltaFVarIds_5049_);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 3, v_postponed_5050_);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 4, v_diag_5051_);
                    v___x_5056_ = v_reuseFailAlloc_5059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5057_ = lean_st_ref_set(v___y_5038_, v___x_5056_);
                v___x_5058_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5058_, 0, v_fst_5045_);
                return v___x_5058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg___boxed(
    mut v_e_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5065_: *mut LeanObject = core::ptr::null_mut();
    v_res_5065_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
        v_e_5062_,
        v___y_5063_,
    );
    lean_dec(v___y_5063_);
    return v_res_5065_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(
    mut v_e_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    v___x_5072_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
        v_e_5066_,
        v___y_5068_,
    );
    return v___x_5072_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___boxed(
    mut v_e_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
    mut v___y_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5079_: *mut LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0(
        v_e_5073_,
        v___y_5074_,
        v___y_5075_,
        v___y_5076_,
        v___y_5077_,
    );
    lean_dec(v___y_5077_);
    lean_dec_ref(v___y_5076_);
    lean_dec(v___y_5075_);
    lean_dec_ref(v___y_5074_);
    return v_res_5079_;
}
pub unsafe fn _init_l_Lean_Linter_List_binders___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    v___x_5083_ = lean_box(0);
    v___x_5084_ = l_Lean_Linter_List_binders___lam__0___closed__1;
    v___x_5085_ = l_Lean_Expr_const___override(v___x_5084_, v___x_5083_);
    return v___x_5085_;
}
pub unsafe fn l_Lean_Linter_List_binders___lam__0(
    mut v_expr_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
    mut v___y_5088_: *mut LeanObject,
    mut v___y_5089_: *mut LeanObject,
    mut v___y_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: u8 = 0;
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5112_: u8 = 0;
    let mut v___x_5113_: u8 = 0;
    let mut v___x_5114_: u8 = 0;
    let mut v_a_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5118_: u8 = 0;
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5096_ = l_Lean_Meta_saveState___redArg(v___y_5088_, v___y_5090_);
                if lean_obj_tag(v___x_5096_) == 0 {
                    v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
                    lean_inc(v_a_5097_);
                    lean_dec_ref_known(v___x_5096_, 1);
                    lean_inc(v___y_5090_);
                    lean_inc(v___y_5088_);
                    v___x_5098_ = lean_infer_type(
                        v_expr_5086_,
                        v___y_5087_,
                        v___y_5088_,
                        v___y_5089_,
                        v___y_5090_,
                    );
                    if lean_obj_tag(v___x_5098_) == 0 {
                        lean_dec(v_a_5097_);
                        lean_dec(v___y_5090_);
                        v___y_5093_ = v___x_5098_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
                        lean_inc(v_a_5099_);
                        v___x_5113_ = l_Lean_Exception_isInterrupt(v_a_5099_);
                        if v___x_5113_ == 0 {
                            v___x_5114_ = l_Lean_Exception_isRuntime(v_a_5099_);
                            v___y_5101_ = v___x_5114_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_a_5099_);
                            v___y_5101_ = v___x_5113_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5090_);
                    lean_dec_ref(v___y_5089_);
                    lean_dec(v___y_5088_);
                    lean_dec_ref(v___y_5087_);
                    lean_dec_ref(v_expr_5086_);
                    v_a_5115_ = lean_ctor_get(v___x_5096_, 0);
                    v_isSharedCheck_5122_ = (!lean_is_exclusive(v___x_5096_)) as u8;
                    if v_isSharedCheck_5122_ == 0 {
                        v___x_5117_ = v___x_5096_;
                        v_isShared_5118_ = v_isSharedCheck_5122_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5115_);
                        lean_dec(v___x_5096_);
                        v___x_5117_ = lean_box(0);
                        v_isShared_5118_ = v_isSharedCheck_5122_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_5093_) == 0 {
                    v_a_5094_ = lean_ctor_get(v___y_5093_, 0);
                    lean_inc(v_a_5094_);
                    lean_dec_ref_known(v___y_5093_, 1);
                    v___x_5095_ =
                        l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(
                            v_a_5094_,
                            v___y_5088_,
                        );
                    lean_dec(v___y_5088_);
                    return v___x_5095_;
                } else {
                    lean_dec(v___y_5088_);
                    return v___y_5093_;
                }
            }
            2 => {
                if v___y_5101_ == 0 {
                    lean_dec_ref_known(v___x_5098_, 1);
                    v___x_5102_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_5097_,
                        v___y_5088_,
                        v___y_5090_,
                    );
                    lean_dec(v___y_5090_);
                    lean_dec(v_a_5097_);
                    if lean_obj_tag(v___x_5102_) == 0 {
                        lean_dec_ref_known(v___x_5102_, 1);
                        v___x_5103_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_List_binders___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_List_binders___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Linter_List_binders___lam__0___closed__2,
                        );
                        v___x_5104_ = l_Lean_instantiateMVars___at___00Lean_Linter_List_binders_spec__0___redArg(v___x_5103_, v___y_5088_);
                        lean_dec(v___y_5088_);
                        return v___x_5104_;
                    } else {
                        lean_dec(v___y_5088_);
                        v_a_5105_ = lean_ctor_get(v___x_5102_, 0);
                        v_isSharedCheck_5112_ = (!lean_is_exclusive(v___x_5102_)) as u8;
                        if v_isSharedCheck_5112_ == 0 {
                            v___x_5107_ = v___x_5102_;
                            v_isShared_5108_ = v_isSharedCheck_5112_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5105_);
                            lean_dec(v___x_5102_);
                            v___x_5107_ = lean_box(0);
                            v_isShared_5108_ = v_isSharedCheck_5112_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5097_);
                    lean_dec(v___y_5090_);
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
                    v_reuseFailAlloc_5111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_a_5105_);
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
                    v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
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
    mut v_expr_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5129_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_p_5130_: *mut LeanObject,
    mut v_ctx_5131_: *mut LeanObject,
    mut v_ti_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isBinder_5134_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5145_: u8 = 0;
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5162_: u8 = 0;
    let mut v_stx_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v_unused_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_a_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isBinder_5134_ = lean_ctor_get_uint8(
                    v_ti_5132_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                if v_isBinder_5134_ == 0 {
                    lean_dec_ref(v_ti_5132_);
                    lean_dec_ref(v_ctx_5131_);
                    lean_dec_ref(v_p_5130_);
                    v___x_5135_ = lean_box(0);
                    v___x_5136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                } else {
                    v_toElabInfo_5137_ = lean_ctor_get(v_ti_5132_, 0);
                    lean_inc_ref(v_toElabInfo_5137_);
                    v_lctx_5138_ = lean_ctor_get(v_ti_5132_, 1);
                    lean_inc_ref_n(v_lctx_5138_, 2);
                    v_expr_5139_ = lean_ctor_get(v_ti_5132_, 3);
                    lean_inc_ref_n(v_expr_5139_, 2);
                    lean_dec_ref(v_ti_5132_);
                    v___f_5140_ = lean_alloc_closure(
                        l_Lean_Linter_List_binders___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___f_5140_, 0, v_expr_5139_);
                    v___x_5141_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_5131_,
                        v_lctx_5138_,
                        v___f_5140_,
                    );
                    if lean_obj_tag(v___x_5141_) == 0 {
                        v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5185_ = (!lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5144_ = v___x_5141_;
                            v_isShared_5145_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5142_);
                            lean_dec(v___x_5141_);
                            v___x_5144_ = lean_box(0);
                            v_isShared_5145_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_expr_5139_);
                        lean_dec_ref(v_lctx_5138_);
                        lean_dec_ref(v_toElabInfo_5137_);
                        lean_dec_ref(v_p_5130_);
                        v_a_5186_ = lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5193_ = (!lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5193_ == 0 {
                            v___x_5188_ = v___x_5141_;
                            v_isShared_5189_ = v_isSharedCheck_5193_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5186_);
                            lean_dec(v___x_5141_);
                            v___x_5188_ = lean_box(0);
                            v_isShared_5189_ = v_isSharedCheck_5193_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_5142_);
                v___x_5146_ = l_Lean_Expr_cleanupAnnotations(v_a_5142_);
                v___x_5147_ = lean_apply_1(v_p_5130_, v___x_5146_);
                v___x_5148_ = (lean_unbox(v___x_5147_) as u8);
                if v___x_5148_ == 0 {
                    lean_dec(v_a_5142_);
                    lean_dec_ref(v_expr_5139_);
                    lean_dec_ref(v_lctx_5138_);
                    lean_dec_ref(v_toElabInfo_5137_);
                    v___x_5149_ = lean_box(0);
                    if v_isShared_5145_ == 0 {
                        lean_ctor_set(v___x_5144_, 0, v___x_5149_);
                        v___x_5151_ = v___x_5144_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
                        v___x_5151_ = v_reuseFailAlloc_5152_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_expr_5139_) == 1 {
                        v_fvarId_5153_ = lean_ctor_get(v_expr_5139_, 0);
                        lean_inc(v_fvarId_5153_);
                        lean_dec_ref_known(v_expr_5139_, 1);
                        v___x_5154_ = lean_local_ctx_find(v_lctx_5138_, v_fvarId_5153_);
                        if lean_obj_tag(v___x_5154_) == 0 {
                            lean_dec(v_a_5142_);
                            lean_dec_ref(v_toElabInfo_5137_);
                            v___x_5155_ = lean_box(0);
                            if v_isShared_5145_ == 0 {
                                lean_ctor_set(v___x_5144_, 0, v___x_5155_);
                                v___x_5157_ = v___x_5144_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
                                v___x_5157_ = v_reuseFailAlloc_5158_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_val_5159_ = lean_ctor_get(v___x_5154_, 0);
                            v_isSharedCheck_5180_ = (!lean_is_exclusive(v___x_5154_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5161_ = v___x_5154_;
                                v_isShared_5162_ = v_isSharedCheck_5180_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_val_5159_);
                                lean_dec(v___x_5154_);
                                v___x_5161_ = lean_box(0);
                                v_isShared_5162_ = v_isSharedCheck_5180_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5142_);
                        lean_dec_ref(v_expr_5139_);
                        lean_dec_ref(v_lctx_5138_);
                        lean_dec_ref(v_toElabInfo_5137_);
                        v___x_5181_ = lean_box(0);
                        if v_isShared_5145_ == 0 {
                            lean_ctor_set(v___x_5144_, 0, v___x_5181_);
                            v___x_5183_ = v___x_5144_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
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
                v_stx_5163_ = lean_ctor_get(v_toElabInfo_5137_, 1);
                v_isSharedCheck_5178_ = (!lean_is_exclusive(v_toElabInfo_5137_)) as u8;
                if v_isSharedCheck_5178_ == 0 {
                    v_unused_5179_ = lean_ctor_get(v_toElabInfo_5137_, 0);
                    lean_dec(v_unused_5179_);
                    v___x_5165_ = v_toElabInfo_5137_;
                    v_isShared_5166_ = v_isSharedCheck_5178_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_stx_5163_);
                    lean_dec(v_toElabInfo_5137_);
                    v___x_5165_ = lean_box(0);
                    v_isShared_5166_ = v_isSharedCheck_5178_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5167_ = l_Lean_LocalDecl_userName(v_val_5159_);
                lean_dec(v_val_5159_);
                if v_isShared_5166_ == 0 {
                    lean_ctor_set(v___x_5165_, 1, v_a_5142_);
                    lean_ctor_set(v___x_5165_, 0, v___x_5167_);
                    v___x_5169_ = v___x_5165_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5167_);
                    lean_ctor_set(v_reuseFailAlloc_5177_, 1, v_a_5142_);
                    v___x_5169_ = v_reuseFailAlloc_5177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5170_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5170_, 0, v_stx_5163_);
                lean_ctor_set(v___x_5170_, 1, v___x_5169_);
                if v_isShared_5162_ == 0 {
                    lean_ctor_set(v___x_5161_, 0, v___x_5170_);
                    v___x_5172_ = v___x_5161_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5170_);
                    v___x_5172_ = v_reuseFailAlloc_5176_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5145_ == 0 {
                    lean_ctor_set(v___x_5144_, 0, v___x_5172_);
                    v___x_5174_ = v___x_5144_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
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
                    v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
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
    mut v_p_5194_: *mut LeanObject,
    mut v_ctx_5195_: *mut LeanObject,
    mut v_ti_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5198_: *mut LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Linter_List_binders___lam__1(v_p_5194_, v_ctx_5195_, v_ti_5196_);
    return v_res_5198_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    v___x_5199_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_5199_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(
    mut v_f_5200_: *mut LeanObject,
    mut v___x_5201_: *mut LeanObject,
    mut v_x_5202_: *mut LeanObject,
    mut v_x_5203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: u8 = 0;
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: usize = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: usize = 0;
    let mut v___x_5223_: usize = 0;
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_vs_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: usize = 0;
    let mut v___x_5241_: usize = 0;
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: usize = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5202_) == 0 {
                    v_cs_5205_ = lean_ctor_get(v_x_5202_, 0);
                    v_isSharedCheck_5225_ = (!lean_is_exclusive(v_x_5202_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5207_ = v_x_5202_;
                        v_isShared_5208_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_5205_);
                        lean_dec(v_x_5202_);
                        v___x_5207_ = lean_box(0);
                        v_isShared_5208_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5226_ = lean_ctor_get(v_x_5202_, 0);
                    v_isSharedCheck_5246_ = (!lean_is_exclusive(v_x_5202_)) as u8;
                    if v_isSharedCheck_5246_ == 0 {
                        v___x_5228_ = v_x_5202_;
                        v_isShared_5229_ = v_isSharedCheck_5246_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_5226_);
                        lean_dec(v_x_5202_);
                        v___x_5228_ = lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5246_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5209_ = lean_unsigned_to_nat(0);
                v___x_5210_ = lean_array_get_size(v_cs_5205_);
                v___x_5211_ = lean_nat_dec_lt(v___x_5209_, v___x_5210_);
                if v___x_5211_ == 0 {
                    lean_dec_ref(v_cs_5205_);
                    lean_dec(v___x_5201_);
                    lean_dec_ref(v_f_5200_);
                    if v_isShared_5208_ == 0 {
                        lean_ctor_set(v___x_5207_, 0, v_x_5203_);
                        v___x_5213_ = v___x_5207_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5214_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_x_5203_);
                        v___x_5213_ = v_reuseFailAlloc_5214_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5215_ = lean_nat_dec_le(v___x_5210_, v___x_5210_);
                    if v___x_5215_ == 0 {
                        if v___x_5211_ == 0 {
                            lean_dec_ref(v_cs_5205_);
                            lean_dec(v___x_5201_);
                            lean_dec_ref(v_f_5200_);
                            if v_isShared_5208_ == 0 {
                                lean_ctor_set(v___x_5207_, 0, v_x_5203_);
                                v___x_5217_ = v___x_5207_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_x_5203_);
                                v___x_5217_ = v_reuseFailAlloc_5218_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5207_);
                            v___x_5219_ = 0usize;
                            v___x_5220_ = lean_usize_of_nat(v___x_5210_);
                            v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5200_, v___x_5201_, v_cs_5205_, v___x_5219_, v___x_5220_, v_x_5203_);
                            lean_dec_ref(v_cs_5205_);
                            return v___x_5221_;
                        }
                    } else {
                        lean_del_object(v___x_5207_);
                        v___x_5222_ = 0usize;
                        v___x_5223_ = lean_usize_of_nat(v___x_5210_);
                        v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5200_, v___x_5201_, v_cs_5205_, v___x_5222_, v___x_5223_, v_x_5203_);
                        lean_dec_ref(v_cs_5205_);
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
                v___x_5230_ = lean_unsigned_to_nat(0);
                v___x_5231_ = lean_array_get_size(v_vs_5226_);
                v___x_5232_ = lean_nat_dec_lt(v___x_5230_, v___x_5231_);
                if v___x_5232_ == 0 {
                    lean_dec_ref(v_vs_5226_);
                    lean_dec(v___x_5201_);
                    lean_dec_ref(v_f_5200_);
                    if v_isShared_5229_ == 0 {
                        lean_ctor_set_tag(v___x_5228_, 0);
                        lean_ctor_set(v___x_5228_, 0, v_x_5203_);
                        v___x_5234_ = v___x_5228_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_x_5203_);
                        v___x_5234_ = v_reuseFailAlloc_5235_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_5236_ = lean_nat_dec_le(v___x_5231_, v___x_5231_);
                    if v___x_5236_ == 0 {
                        if v___x_5232_ == 0 {
                            lean_dec_ref(v_vs_5226_);
                            lean_dec(v___x_5201_);
                            lean_dec_ref(v_f_5200_);
                            if v_isShared_5229_ == 0 {
                                lean_ctor_set_tag(v___x_5228_, 0);
                                lean_ctor_set(v___x_5228_, 0, v_x_5203_);
                                v___x_5238_ = v___x_5228_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_x_5203_);
                                v___x_5238_ = v_reuseFailAlloc_5239_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5228_);
                            v___x_5240_ = 0usize;
                            v___x_5241_ = lean_usize_of_nat(v___x_5231_);
                            v___x_5242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5200_, v___x_5201_, v_vs_5226_, v___x_5240_, v___x_5241_, v_x_5203_);
                            lean_dec_ref(v_vs_5226_);
                            return v___x_5242_;
                        }
                    } else {
                        lean_del_object(v___x_5228_);
                        v___x_5243_ = 0usize;
                        v___x_5244_ = lean_usize_of_nat(v___x_5231_);
                        v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5200_, v___x_5201_, v_vs_5226_, v___x_5243_, v___x_5244_, v_x_5203_);
                        lean_dec_ref(v_vs_5226_);
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
    mut v_f_5247_: *mut LeanObject,
    mut v___x_5248_: *mut LeanObject,
    mut v_as_5249_: *mut LeanObject,
    mut v_i_5250_: usize,
    mut v_stop_5251_: usize,
    mut v_b_5252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: usize = 0;
    let mut v___x_5259_: usize = 0;
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5254_ = lean_usize_dec_eq(v_i_5250_, v_stop_5251_);
                if v___x_5254_ == 0 {
                    v___x_5255_ = lean_array_uget_borrowed(v_as_5249_, v_i_5250_);
                    lean_inc(v___x_5255_);
                    lean_inc(v___x_5248_);
                    lean_inc_ref(v_f_5247_);
                    v___x_5256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5247_, v___x_5248_, v___x_5255_, v_b_5252_);
                    if lean_obj_tag(v___x_5256_) == 0 {
                        v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
                        lean_inc(v_a_5257_);
                        lean_dec_ref_known(v___x_5256_, 1);
                        v___x_5258_ = 1usize;
                        v___x_5259_ = lean_usize_add(v_i_5250_, v___x_5258_);
                        v_i_5250_ = v___x_5259_;
                        v_b_5252_ = v_a_5257_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_5248_);
                        lean_dec_ref(v_f_5247_);
                        return v___x_5256_;
                    }
                } else {
                    lean_dec(v___x_5248_);
                    lean_dec_ref(v_f_5247_);
                    v___x_5261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5261_, 0, v_b_5252_);
                    return v___x_5261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_f_5262_: *mut LeanObject,
    mut v___x_5263_: *mut LeanObject,
    mut v_x_5264_: *mut LeanObject,
    mut v_x_5265_: usize,
    mut v_x_5266_: usize,
    mut v_x_5267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: usize = 0;
    let mut v_j_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: usize = 0;
    let mut v___x_5275_: usize = 0;
    let mut v___x_5276_: usize = 0;
    let mut v___x_5277_: usize = 0;
    let mut v___x_5278_: usize = 0;
    let mut v___x_5279_: usize = 0;
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: usize = 0;
    let mut v___x_5288_: usize = 0;
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: usize = 0;
    let mut v___x_5291_: usize = 0;
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: u8 = 0;
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: u8 = 0;
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: usize = 0;
    let mut v___x_5308_: usize = 0;
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5264_) == 0 {
                    v_cs_5269_ = lean_ctor_get(v_x_5264_, 0);
                    lean_inc_ref(v_cs_5269_);
                    lean_dec_ref_known(v_x_5264_, 1);
                    v___x_5270_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
                    v___x_5271_ = lean_usize_shift_right(v_x_5265_, v_x_5266_);
                    v_j_5272_ = lean_usize_to_nat(v___x_5271_);
                    v___x_5273_ = lean_array_get_borrowed(v___x_5270_, v_cs_5269_, v_j_5272_);
                    v___x_5274_ = 1usize;
                    v___x_5275_ = lean_usize_shift_left(v___x_5274_, v_x_5266_);
                    v___x_5276_ = lean_usize_sub(v___x_5275_, v___x_5274_);
                    v___x_5277_ = lean_usize_land(v_x_5265_, v___x_5276_);
                    v___x_5278_ = 5usize;
                    v___x_5279_ = lean_usize_sub(v_x_5266_, v___x_5278_);
                    lean_inc(v___x_5273_);
                    lean_inc(v___x_5263_);
                    lean_inc_ref(v_f_5262_);
                    v___x_5280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5262_, v___x_5263_, v___x_5273_, v___x_5277_, v___x_5279_, v_x_5267_);
                    if lean_obj_tag(v___x_5280_) == 0 {
                        v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
                        lean_inc(v_a_5281_);
                        v___x_5282_ = lean_unsigned_to_nat(1);
                        v___x_5283_ = lean_nat_add(v_j_5272_, v___x_5282_);
                        lean_dec(v_j_5272_);
                        v___x_5284_ = lean_array_get_size(v_cs_5269_);
                        v___x_5285_ = lean_nat_dec_lt(v___x_5283_, v___x_5284_);
                        if v___x_5285_ == 0 {
                            lean_dec(v___x_5283_);
                            lean_dec(v_a_5281_);
                            lean_dec_ref(v_cs_5269_);
                            lean_dec(v___x_5263_);
                            lean_dec_ref(v_f_5262_);
                            return v___x_5280_;
                        } else {
                            v___x_5286_ = lean_nat_dec_le(v___x_5284_, v___x_5284_);
                            if v___x_5286_ == 0 {
                                if v___x_5285_ == 0 {
                                    lean_dec(v___x_5283_);
                                    lean_dec(v_a_5281_);
                                    lean_dec_ref(v_cs_5269_);
                                    lean_dec(v___x_5263_);
                                    lean_dec_ref(v_f_5262_);
                                    return v___x_5280_;
                                } else {
                                    lean_dec_ref_known(v___x_5280_, 1);
                                    v___x_5287_ = lean_usize_of_nat(v___x_5283_);
                                    lean_dec(v___x_5283_);
                                    v___x_5288_ = lean_usize_of_nat(v___x_5284_);
                                    v___x_5289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5262_, v___x_5263_, v_cs_5269_, v___x_5287_, v___x_5288_, v_a_5281_);
                                    lean_dec_ref(v_cs_5269_);
                                    return v___x_5289_;
                                }
                            } else {
                                lean_dec_ref_known(v___x_5280_, 1);
                                v___x_5290_ = lean_usize_of_nat(v___x_5283_);
                                lean_dec(v___x_5283_);
                                v___x_5291_ = lean_usize_of_nat(v___x_5284_);
                                v___x_5292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5262_, v___x_5263_, v_cs_5269_, v___x_5290_, v___x_5291_, v_a_5281_);
                                lean_dec_ref(v_cs_5269_);
                                return v___x_5292_;
                            }
                        }
                    } else {
                        lean_dec(v_j_5272_);
                        lean_dec_ref(v_cs_5269_);
                        lean_dec(v___x_5263_);
                        lean_dec_ref(v_f_5262_);
                        return v___x_5280_;
                    }
                } else {
                    v_vs_5293_ = lean_ctor_get(v_x_5264_, 0);
                    v_isSharedCheck_5313_ = (!lean_is_exclusive(v_x_5264_)) as u8;
                    if v_isSharedCheck_5313_ == 0 {
                        v___x_5295_ = v_x_5264_;
                        v_isShared_5296_ = v_isSharedCheck_5313_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vs_5293_);
                        lean_dec(v_x_5264_);
                        v___x_5295_ = lean_box(0);
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
                    lean_dec(v___x_5297_);
                    lean_dec_ref(v_vs_5293_);
                    lean_dec(v___x_5263_);
                    lean_dec_ref(v_f_5262_);
                    if v_isShared_5296_ == 0 {
                        lean_ctor_set_tag(v___x_5295_, 0);
                        lean_ctor_set(v___x_5295_, 0, v_x_5267_);
                        v___x_5301_ = v___x_5295_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_x_5267_);
                        v___x_5301_ = v_reuseFailAlloc_5302_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5303_ = lean_nat_dec_le(v___x_5298_, v___x_5298_);
                    if v___x_5303_ == 0 {
                        if v___x_5299_ == 0 {
                            lean_dec(v___x_5297_);
                            lean_dec_ref(v_vs_5293_);
                            lean_dec(v___x_5263_);
                            lean_dec_ref(v_f_5262_);
                            if v_isShared_5296_ == 0 {
                                lean_ctor_set_tag(v___x_5295_, 0);
                                lean_ctor_set(v___x_5295_, 0, v_x_5267_);
                                v___x_5305_ = v___x_5295_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_x_5267_);
                                v___x_5305_ = v_reuseFailAlloc_5306_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5295_);
                            v___x_5307_ = lean_usize_of_nat(v___x_5297_);
                            lean_dec(v___x_5297_);
                            v___x_5308_ = lean_usize_of_nat(v___x_5298_);
                            v___x_5309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5262_, v___x_5263_, v_vs_5293_, v___x_5307_, v___x_5308_, v_x_5267_);
                            lean_dec_ref(v_vs_5293_);
                            return v___x_5309_;
                        }
                    } else {
                        lean_del_object(v___x_5295_);
                        v___x_5310_ = lean_usize_of_nat(v___x_5297_);
                        lean_dec(v___x_5297_);
                        v___x_5311_ = lean_usize_of_nat(v___x_5298_);
                        v___x_5312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5262_, v___x_5263_, v_vs_5293_, v___x_5310_, v___x_5311_, v_x_5267_);
                        lean_dec_ref(v_vs_5293_);
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
    mut v_f_5314_: *mut LeanObject,
    mut v___x_5315_: *mut LeanObject,
    mut v_t_5316_: *mut LeanObject,
    mut v_init_5317_: *mut LeanObject,
    mut v_start_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: u8 = 0;
    v___x_5320_ = lean_unsigned_to_nat(0);
    v___x_5321_ = lean_nat_dec_eq(v_start_5318_, v___x_5320_);
    if v___x_5321_ == 0 {
        let mut v_root_5322_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5323_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_5324_: usize = 0;
        let mut v_tailOff_5325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5326_: u8 = 0;
        v_root_5322_ = lean_ctor_get(v_t_5316_, 0);
        lean_inc_ref(v_root_5322_);
        v_tail_5323_ = lean_ctor_get(v_t_5316_, 1);
        lean_inc_ref(v_tail_5323_);
        v_shift_5324_ = lean_ctor_get_usize(v_t_5316_, 4);
        v_tailOff_5325_ = lean_ctor_get(v_t_5316_, 3);
        lean_inc(v_tailOff_5325_);
        lean_dec_ref(v_t_5316_);
        v___x_5326_ = lean_nat_dec_le(v_tailOff_5325_, v_start_5318_);
        if v___x_5326_ == 0 {
            let mut v___x_5327_: usize = 0;
            let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_5325_);
            v___x_5327_ = lean_usize_of_nat(v_start_5318_);
            lean_inc(v___x_5315_);
            lean_inc_ref(v_f_5314_);
            v___x_5328_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5314_, v___x_5315_, v_root_5322_, v___x_5327_, v_shift_5324_, v_init_5317_);
            if lean_obj_tag(v___x_5328_) == 0 {
                let mut v_a_5329_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5331_: u8 = 0;
                v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
                lean_inc(v_a_5329_);
                v___x_5330_ = lean_array_get_size(v_tail_5323_);
                v___x_5331_ = lean_nat_dec_lt(v___x_5320_, v___x_5330_);
                if v___x_5331_ == 0 {
                    lean_dec(v_a_5329_);
                    lean_dec_ref(v_tail_5323_);
                    lean_dec(v___x_5315_);
                    lean_dec_ref(v_f_5314_);
                    return v___x_5328_;
                } else {
                    let mut v___x_5332_: u8 = 0;
                    v___x_5332_ = lean_nat_dec_le(v___x_5330_, v___x_5330_);
                    if v___x_5332_ == 0 {
                        if v___x_5331_ == 0 {
                            lean_dec(v_a_5329_);
                            lean_dec_ref(v_tail_5323_);
                            lean_dec(v___x_5315_);
                            lean_dec_ref(v_f_5314_);
                            return v___x_5328_;
                        } else {
                            let mut v___x_5333_: usize = 0;
                            let mut v___x_5334_: usize = 0;
                            let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_5328_, 1);
                            v___x_5333_ = 0usize;
                            v___x_5334_ = lean_usize_of_nat(v___x_5330_);
                            v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5333_, v___x_5334_, v_a_5329_);
                            lean_dec_ref(v_tail_5323_);
                            return v___x_5335_;
                        }
                    } else {
                        let mut v___x_5336_: usize = 0;
                        let mut v___x_5337_: usize = 0;
                        let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_5328_, 1);
                        v___x_5336_ = 0usize;
                        v___x_5337_ = lean_usize_of_nat(v___x_5330_);
                        v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5336_, v___x_5337_, v_a_5329_);
                        lean_dec_ref(v_tail_5323_);
                        return v___x_5338_;
                    }
                }
            } else {
                lean_dec_ref(v_tail_5323_);
                lean_dec(v___x_5315_);
                lean_dec_ref(v_f_5314_);
                return v___x_5328_;
            }
        } else {
            let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5341_: u8 = 0;
            lean_dec_ref(v_root_5322_);
            v___x_5339_ = lean_nat_sub(v_start_5318_, v_tailOff_5325_);
            lean_dec(v_tailOff_5325_);
            v___x_5340_ = lean_array_get_size(v_tail_5323_);
            v___x_5341_ = lean_nat_dec_lt(v___x_5339_, v___x_5340_);
            if v___x_5341_ == 0 {
                let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_5339_);
                lean_dec_ref(v_tail_5323_);
                lean_dec(v___x_5315_);
                lean_dec_ref(v_f_5314_);
                v___x_5342_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5342_, 0, v_init_5317_);
                return v___x_5342_;
            } else {
                let mut v___x_5343_: u8 = 0;
                v___x_5343_ = lean_nat_dec_le(v___x_5340_, v___x_5340_);
                if v___x_5343_ == 0 {
                    if v___x_5341_ == 0 {
                        let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_5339_);
                        lean_dec_ref(v_tail_5323_);
                        lean_dec(v___x_5315_);
                        lean_dec_ref(v_f_5314_);
                        v___x_5344_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5344_, 0, v_init_5317_);
                        return v___x_5344_;
                    } else {
                        let mut v___x_5345_: usize = 0;
                        let mut v___x_5346_: usize = 0;
                        let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5345_ = lean_usize_of_nat(v___x_5339_);
                        lean_dec(v___x_5339_);
                        v___x_5346_ = lean_usize_of_nat(v___x_5340_);
                        v___x_5347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5345_, v___x_5346_, v_init_5317_);
                        lean_dec_ref(v_tail_5323_);
                        return v___x_5347_;
                    }
                } else {
                    let mut v___x_5348_: usize = 0;
                    let mut v___x_5349_: usize = 0;
                    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5348_ = lean_usize_of_nat(v___x_5339_);
                    lean_dec(v___x_5339_);
                    v___x_5349_ = lean_usize_of_nat(v___x_5340_);
                    v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5323_, v___x_5348_, v___x_5349_, v_init_5317_);
                    lean_dec_ref(v_tail_5323_);
                    return v___x_5350_;
                }
            }
        }
    } else {
        let mut v_root_5351_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
        v_root_5351_ = lean_ctor_get(v_t_5316_, 0);
        lean_inc_ref(v_root_5351_);
        v_tail_5352_ = lean_ctor_get(v_t_5316_, 1);
        lean_inc_ref(v_tail_5352_);
        lean_dec_ref(v_t_5316_);
        lean_inc(v___x_5315_);
        lean_inc_ref(v_f_5314_);
        v___x_5353_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5314_, v___x_5315_, v_root_5351_, v_init_5317_);
        if lean_obj_tag(v___x_5353_) == 0 {
            let mut v_a_5354_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5356_: u8 = 0;
            v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
            lean_inc(v_a_5354_);
            v___x_5355_ = lean_array_get_size(v_tail_5352_);
            v___x_5356_ = lean_nat_dec_lt(v___x_5320_, v___x_5355_);
            if v___x_5356_ == 0 {
                lean_dec(v_a_5354_);
                lean_dec_ref(v_tail_5352_);
                lean_dec(v___x_5315_);
                lean_dec_ref(v_f_5314_);
                return v___x_5353_;
            } else {
                let mut v___x_5357_: u8 = 0;
                v___x_5357_ = lean_nat_dec_le(v___x_5355_, v___x_5355_);
                if v___x_5357_ == 0 {
                    if v___x_5356_ == 0 {
                        lean_dec(v_a_5354_);
                        lean_dec_ref(v_tail_5352_);
                        lean_dec(v___x_5315_);
                        lean_dec_ref(v_f_5314_);
                        return v___x_5353_;
                    } else {
                        let mut v___x_5358_: usize = 0;
                        let mut v___x_5359_: usize = 0;
                        let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_5353_, 1);
                        v___x_5358_ = 0usize;
                        v___x_5359_ = lean_usize_of_nat(v___x_5355_);
                        v___x_5360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5352_, v___x_5358_, v___x_5359_, v_a_5354_);
                        lean_dec_ref(v_tail_5352_);
                        return v___x_5360_;
                    }
                } else {
                    let mut v___x_5361_: usize = 0;
                    let mut v___x_5362_: usize = 0;
                    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_5353_, 1);
                    v___x_5361_ = 0usize;
                    v___x_5362_ = lean_usize_of_nat(v___x_5355_);
                    v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5314_, v___x_5315_, v_tail_5352_, v___x_5361_, v___x_5362_, v_a_5354_);
                    lean_dec_ref(v_tail_5352_);
                    return v___x_5363_;
                }
            }
        } else {
            lean_dec_ref(v_tail_5352_);
            lean_dec(v___x_5315_);
            lean_dec_ref(v_f_5314_);
            return v___x_5353_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(
    mut v_f_5364_: *mut LeanObject,
    mut v_ctx_x3f_5365_: *mut LeanObject,
    mut v_a_5366_: *mut LeanObject,
    mut v_x_5367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut v_unused_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_5367_) {
                0 => {
                    v_i_5369_ = lean_ctor_get(v_x_5367_, 0);
                    lean_inc_ref(v_i_5369_);
                    v_t_5370_ = lean_ctor_get(v_x_5367_, 1);
                    lean_inc_ref(v_t_5370_);
                    lean_dec_ref_known(v_x_5367_, 2);
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
                    v_i_5373_ = lean_ctor_get(v_x_5367_, 0);
                    lean_inc_ref(v_i_5373_);
                    v_children_5374_ = lean_ctor_get(v_x_5367_, 1);
                    lean_inc_ref(v_children_5374_);
                    lean_dec_ref_known(v_x_5367_, 2);
                    if lean_obj_tag(v_ctx_x3f_5365_) == 0 {
                        v_a_5376_ = v_a_5366_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5380_ = lean_ctor_get(v_ctx_x3f_5365_, 0);
                        lean_inc_ref(v_f_5364_);
                        lean_inc_ref(v_i_5373_);
                        lean_inc(v_val_5380_);
                        v___x_5381_ =
                            lean_apply_4(v_f_5364_, v_val_5380_, v_i_5373_, v_a_5366_, lean_box(0));
                        if lean_obj_tag(v___x_5381_) == 0 {
                            v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
                            lean_inc(v_a_5382_);
                            lean_dec_ref_known(v___x_5381_, 1);
                            v_a_5376_ = v_a_5382_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref_known(v_ctx_x3f_5365_, 1);
                            lean_dec_ref(v_children_5374_);
                            lean_dec_ref(v_i_5373_);
                            lean_dec_ref(v_f_5364_);
                            return v___x_5381_;
                        }
                    }
                }
                _ => {
                    lean_dec(v_ctx_x3f_5365_);
                    lean_dec_ref(v_f_5364_);
                    v_isSharedCheck_5389_ = (!lean_is_exclusive(v_x_5367_)) as u8;
                    if v_isSharedCheck_5389_ == 0 {
                        v_unused_5390_ = lean_ctor_get(v_x_5367_, 0);
                        lean_dec(v_unused_5390_);
                        v___x_5384_ = v_x_5367_;
                        v_isShared_5385_ = v_isSharedCheck_5389_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_x_5367_);
                        v___x_5384_ = lean_box(0);
                        v_isShared_5385_ = v_isSharedCheck_5389_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5377_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_5365_, v_i_5373_);
                lean_dec_ref(v_i_5373_);
                v___x_5378_ = lean_unsigned_to_nat(0);
                v___x_5379_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5364_, v___x_5377_, v_children_5374_, v_a_5376_, v___x_5378_);
                return v___x_5379_;
            }
            2 => {
                if v_isShared_5385_ == 0 {
                    lean_ctor_set_tag(v___x_5384_, 0);
                    lean_ctor_set(v___x_5384_, 0, v_a_5366_);
                    v___x_5387_ = v___x_5384_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5366_);
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
    mut v_f_5391_: *mut LeanObject,
    mut v___x_5392_: *mut LeanObject,
    mut v_as_5393_: *mut LeanObject,
    mut v_i_5394_: usize,
    mut v_stop_5395_: usize,
    mut v_b_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5398_: u8 = 0;
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: usize = 0;
    let mut v___x_5403_: usize = 0;
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5398_ = lean_usize_dec_eq(v_i_5394_, v_stop_5395_);
                if v___x_5398_ == 0 {
                    v___x_5399_ = lean_array_uget_borrowed(v_as_5393_, v_i_5394_);
                    lean_inc(v___x_5399_);
                    lean_inc(v___x_5392_);
                    lean_inc_ref(v_f_5391_);
                    v___x_5400_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5391_, v___x_5392_, v_b_5396_, v___x_5399_);
                    if lean_obj_tag(v___x_5400_) == 0 {
                        v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
                        lean_inc(v_a_5401_);
                        lean_dec_ref_known(v___x_5400_, 1);
                        v___x_5402_ = 1usize;
                        v___x_5403_ = lean_usize_add(v_i_5394_, v___x_5402_);
                        v_i_5394_ = v___x_5403_;
                        v_b_5396_ = v_a_5401_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_5392_);
                        lean_dec_ref(v_f_5391_);
                        return v___x_5400_;
                    }
                } else {
                    lean_dec(v___x_5392_);
                    lean_dec_ref(v_f_5391_);
                    v___x_5405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5405_, 0, v_b_5396_);
                    return v___x_5405_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_f_5406_: *mut LeanObject,
    mut v___x_5407_: *mut LeanObject,
    mut v_as_5408_: *mut LeanObject,
    mut v_i_5409_: *mut LeanObject,
    mut v_stop_5410_: *mut LeanObject,
    mut v_b_5411_: *mut LeanObject,
    mut v___y_5412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5413_: usize = 0;
    let mut v_stop_boxed_5414_: usize = 0;
    let mut v_res_5415_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5413_ = lean_unbox_usize(v_i_5409_);
    lean_dec(v_i_5409_);
    v_stop_boxed_5414_ = lean_unbox_usize(v_stop_5410_);
    lean_dec(v_stop_5410_);
    v_res_5415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5406_, v___x_5407_, v_as_5408_, v_i_boxed_5413_, v_stop_boxed_5414_, v_b_5411_);
    lean_dec_ref(v_as_5408_);
    return v_res_5415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_f_5416_: *mut LeanObject,
    mut v___x_5417_: *mut LeanObject,
    mut v_as_5418_: *mut LeanObject,
    mut v_i_5419_: *mut LeanObject,
    mut v_stop_5420_: *mut LeanObject,
    mut v_b_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5423_: usize = 0;
    let mut v_stop_boxed_5424_: usize = 0;
    let mut v_res_5425_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5423_ = lean_unbox_usize(v_i_5419_);
    lean_dec(v_i_5419_);
    v_stop_boxed_5424_ = lean_unbox_usize(v_stop_5420_);
    lean_dec(v_stop_5420_);
    v_res_5425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5416_, v___x_5417_, v_as_5418_, v_i_boxed_5423_, v_stop_boxed_5424_, v_b_5421_);
    lean_dec_ref(v_as_5418_);
    return v_res_5425_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_5426_: *mut LeanObject,
    mut v_ctx_x3f_5427_: *mut LeanObject,
    mut v_a_5428_: *mut LeanObject,
    mut v_x_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5431_: *mut LeanObject = core::ptr::null_mut();
    v_res_5431_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5426_, v_ctx_x3f_5427_, v_a_5428_, v_x_5429_);
    return v_res_5431_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_f_5432_: *mut LeanObject,
    mut v___x_5433_: *mut LeanObject,
    mut v_x_5434_: *mut LeanObject,
    mut v_x_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5437_: *mut LeanObject = core::ptr::null_mut();
    v_res_5437_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5432_, v___x_5433_, v_x_5434_, v_x_5435_);
    return v_res_5437_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_f_5438_: *mut LeanObject,
    mut v___x_5439_: *mut LeanObject,
    mut v_x_5440_: *mut LeanObject,
    mut v_x_5441_: *mut LeanObject,
    mut v_x_5442_: *mut LeanObject,
    mut v_x_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2919__boxed_5445_: usize = 0;
    let mut v_x_2920__boxed_5446_: usize = 0;
    let mut v_res_5447_: *mut LeanObject = core::ptr::null_mut();
    v_x_2919__boxed_5445_ = lean_unbox_usize(v_x_5441_);
    lean_dec(v_x_5441_);
    v_x_2920__boxed_5446_ = lean_unbox_usize(v_x_5442_);
    lean_dec(v_x_5442_);
    v_res_5447_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5438_, v___x_5439_, v_x_5440_, v_x_2919__boxed_5445_, v_x_2920__boxed_5446_, v_x_5443_);
    return v_res_5447_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_f_5448_: *mut LeanObject,
    mut v___x_5449_: *mut LeanObject,
    mut v_t_5450_: *mut LeanObject,
    mut v_init_5451_: *mut LeanObject,
    mut v_start_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5454_: *mut LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5448_, v___x_5449_, v_t_5450_, v_init_5451_, v_start_5452_);
    lean_dec(v_start_5452_);
    return v_res_5454_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(
    mut v_f_5455_: *mut LeanObject,
    mut v_init_5456_: *mut LeanObject,
    mut v_x_5457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    v___x_5459_ = lean_box(0);
    v___x_5460_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5455_, v___x_5459_, v_init_5456_, v_x_5457_);
    return v___x_5460_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg___boxed(
    mut v_f_5461_: *mut LeanObject,
    mut v_init_5462_: *mut LeanObject,
    mut v_x_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5465_: *mut LeanObject = core::ptr::null_mut();
    v_res_5465_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_5461_, v_init_5462_, v_x_5463_);
    return v_res_5465_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(
    mut v_f_5466_: *mut LeanObject,
    mut v_ctx_5467_: *mut LeanObject,
    mut v_info_5468_: *mut LeanObject,
    mut v_result_5469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5485_: u8 = 0;
    let mut v_a_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_5468_) == 1 {
                    v_i_5471_ = lean_ctor_get(v_info_5468_, 0);
                    lean_inc_ref(v_i_5471_);
                    lean_dec_ref_known(v_info_5468_, 1);
                    v___x_5472_ = lean_apply_3(v_f_5466_, v_ctx_5467_, v_i_5471_, lean_box(0));
                    if lean_obj_tag(v___x_5472_) == 0 {
                        v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5485_ = (!lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5485_ == 0 {
                            v___x_5475_ = v___x_5472_;
                            v_isShared_5476_ = v_isSharedCheck_5485_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5473_);
                            lean_dec(v___x_5472_);
                            v___x_5475_ = lean_box(0);
                            v_isShared_5476_ = v_isSharedCheck_5485_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_result_5469_);
                        v_a_5486_ = lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5493_ = (!lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5493_ == 0 {
                            v___x_5488_ = v___x_5472_;
                            v_isShared_5489_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5486_);
                            lean_dec(v___x_5472_);
                            v___x_5488_ = lean_box(0);
                            v_isShared_5489_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_info_5468_);
                    lean_dec_ref(v_ctx_5467_);
                    lean_dec_ref(v_f_5466_);
                    v___x_5494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5494_, 0, v_result_5469_);
                    return v___x_5494_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5473_) == 0 {
                    if v_isShared_5476_ == 0 {
                        lean_ctor_set(v___x_5475_, 0, v_result_5469_);
                        v___x_5478_ = v___x_5475_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_result_5469_);
                        v___x_5478_ = v_reuseFailAlloc_5479_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5480_ = lean_ctor_get(v_a_5473_, 0);
                    lean_inc(v_val_5480_);
                    lean_dec_ref_known(v_a_5473_, 1);
                    v___x_5481_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5481_, 0, v_val_5480_);
                    lean_ctor_set(v___x_5481_, 1, v_result_5469_);
                    if v_isShared_5476_ == 0 {
                        lean_ctor_set(v___x_5475_, 0, v___x_5481_);
                        v___x_5483_ = v___x_5475_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
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
                    v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
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
    mut v_f_5495_: *mut LeanObject,
    mut v_ctx_5496_: *mut LeanObject,
    mut v_info_5497_: *mut LeanObject,
    mut v_result_5498_: *mut LeanObject,
    mut v___y_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5500_: *mut LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0(v_f_5495_, v_ctx_5496_, v_info_5497_, v_result_5498_);
    return v_res_5500_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
    mut v_t_5501_: *mut LeanObject,
    mut v_f_5502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    v___f_5504_ = lean_alloc_closure(l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
    lean_closure_set(v___f_5504_, 0, v_f_5502_);
    v___x_5505_ = lean_box(0);
    v___x_5506_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v___f_5504_, v___x_5505_, v_t_5501_);
    return v___x_5506_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg___boxed(
    mut v_t_5507_: *mut LeanObject,
    mut v_f_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5510_: *mut LeanObject = core::ptr::null_mut();
    v_res_5510_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5507_, v_f_5508_,
        );
    return v_res_5510_;
}
pub unsafe fn l_Lean_Linter_List_binders(
    mut v_t_5511_: *mut LeanObject,
    mut v_p_5512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    v___f_5514_ = lean_alloc_closure(
        l_Lean_Linter_List_binders___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5514_, 0, v_p_5512_);
    v___x_5515_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5511_,
            v___f_5514_,
        );
    return v___x_5515_;
}
pub unsafe fn l_Lean_Linter_List_binders___boxed(
    mut v_t_5516_: *mut LeanObject,
    mut v_p_5517_: *mut LeanObject,
    mut v_a_5518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5519_: *mut LeanObject = core::ptr::null_mut();
    v_res_5519_ = l_Lean_Linter_List_binders(v_t_5516_, v_p_5517_);
    return v_res_5519_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(
    mut v_00_u03b1_5520_: *mut LeanObject,
    mut v_t_5521_: *mut LeanObject,
    mut v_f_5522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    v___x_5524_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___redArg(
            v_t_5521_, v_f_5522_,
        );
    return v___x_5524_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1___boxed(
    mut v_00_u03b1_5525_: *mut LeanObject,
    mut v_t_5526_: *mut LeanObject,
    mut v_f_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5529_: *mut LeanObject = core::ptr::null_mut();
    v_res_5529_ = l_Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1(
        v_00_u03b1_5525_,
        v_t_5526_,
        v_f_5527_,
    );
    return v_res_5529_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(
    mut v_00_u03b1_5530_: *mut LeanObject,
    mut v_f_5531_: *mut LeanObject,
    mut v_init_5532_: *mut LeanObject,
    mut v_x_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    v___x_5535_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___redArg(v_f_5531_, v_init_5532_, v_x_5533_);
    return v___x_5535_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1___boxed(
    mut v_00_u03b1_5536_: *mut LeanObject,
    mut v_f_5537_: *mut LeanObject,
    mut v_init_5538_: *mut LeanObject,
    mut v_x_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5541_: *mut LeanObject = core::ptr::null_mut();
    v_res_5541_ = l_Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1(v_00_u03b1_5536_, v_f_5537_, v_init_5538_, v_x_5539_);
    return v_res_5541_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(
    mut v_00_u03b1_5542_: *mut LeanObject,
    mut v_f_5543_: *mut LeanObject,
    mut v_ctx_x3f_5544_: *mut LeanObject,
    mut v_a_5545_: *mut LeanObject,
    mut v_x_5546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    v___x_5548_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___redArg(v_f_5543_, v_ctx_x3f_5544_, v_a_5545_, v_x_5546_);
    return v___x_5548_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_5549_: *mut LeanObject,
    mut v_f_5550_: *mut LeanObject,
    mut v_ctx_x3f_5551_: *mut LeanObject,
    mut v_a_5552_: *mut LeanObject,
    mut v_x_5553_: *mut LeanObject,
    mut v___y_5554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5555_: *mut LeanObject = core::ptr::null_mut();
    v_res_5555_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2(v_00_u03b1_5549_, v_f_5550_, v_ctx_x3f_5551_, v_a_5552_, v_x_5553_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_5556_: *mut LeanObject,
    mut v_f_5557_: *mut LeanObject,
    mut v___x_5558_: *mut LeanObject,
    mut v_t_5559_: *mut LeanObject,
    mut v_init_5560_: *mut LeanObject,
    mut v_start_5561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___redArg(v_f_5557_, v___x_5558_, v_t_5559_, v_init_5560_, v_start_5561_);
    return v___x_5563_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_5564_: *mut LeanObject,
    mut v_f_5565_: *mut LeanObject,
    mut v___x_5566_: *mut LeanObject,
    mut v_t_5567_: *mut LeanObject,
    mut v_init_5568_: *mut LeanObject,
    mut v_start_5569_: *mut LeanObject,
    mut v___y_5570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5571_: *mut LeanObject = core::ptr::null_mut();
    v_res_5571_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_5564_, v_f_5565_, v___x_5566_, v_t_5567_, v_init_5568_, v_start_5569_);
    lean_dec(v_start_5569_);
    return v_res_5571_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b1_5572_: *mut LeanObject,
    mut v_f_5573_: *mut LeanObject,
    mut v___x_5574_: *mut LeanObject,
    mut v_x_5575_: *mut LeanObject,
    mut v_x_5576_: usize,
    mut v_x_5577_: usize,
    mut v_x_5578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    v___x_5580_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_f_5573_, v___x_5574_, v_x_5575_, v_x_5576_, v_x_5577_, v_x_5578_);
    return v___x_5580_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_5581_: *mut LeanObject,
    mut v_f_5582_: *mut LeanObject,
    mut v___x_5583_: *mut LeanObject,
    mut v_x_5584_: *mut LeanObject,
    mut v_x_5585_: *mut LeanObject,
    mut v_x_5586_: *mut LeanObject,
    mut v_x_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3339__boxed_5589_: usize = 0;
    let mut v_x_3340__boxed_5590_: usize = 0;
    let mut v_res_5591_: *mut LeanObject = core::ptr::null_mut();
    v_x_3339__boxed_5589_ = lean_unbox_usize(v_x_5585_);
    lean_dec(v_x_5585_);
    v_x_3340__boxed_5590_ = lean_unbox_usize(v_x_5586_);
    lean_dec(v_x_5586_);
    v_res_5591_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_5581_, v_f_5582_, v___x_5583_, v_x_5584_, v_x_3339__boxed_5589_, v_x_3340__boxed_5590_, v_x_5587_);
    return v_res_5591_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_5592_: *mut LeanObject,
    mut v_f_5593_: *mut LeanObject,
    mut v___x_5594_: *mut LeanObject,
    mut v_as_5595_: *mut LeanObject,
    mut v_i_5596_: usize,
    mut v_stop_5597_: usize,
    mut v_b_5598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    v___x_5600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_f_5593_, v___x_5594_, v_as_5595_, v_i_5596_, v_stop_5597_, v_b_5598_);
    return v___x_5600_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_5601_: *mut LeanObject,
    mut v_f_5602_: *mut LeanObject,
    mut v___x_5603_: *mut LeanObject,
    mut v_as_5604_: *mut LeanObject,
    mut v_i_5605_: *mut LeanObject,
    mut v_stop_5606_: *mut LeanObject,
    mut v_b_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5609_: usize = 0;
    let mut v_stop_boxed_5610_: usize = 0;
    let mut v_res_5611_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5609_ = lean_unbox_usize(v_i_5605_);
    lean_dec(v_i_5605_);
    v_stop_boxed_5610_ = lean_unbox_usize(v_stop_5606_);
    lean_dec(v_stop_5606_);
    v_res_5611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_5601_, v_f_5602_, v___x_5603_, v_as_5604_, v_i_boxed_5609_, v_stop_boxed_5610_, v_b_5607_);
    lean_dec_ref(v_as_5604_);
    return v_res_5611_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(
    mut v_00_u03b1_5612_: *mut LeanObject,
    mut v_f_5613_: *mut LeanObject,
    mut v___x_5614_: *mut LeanObject,
    mut v_x_5615_: *mut LeanObject,
    mut v_x_5616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    v___x_5618_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___redArg(v_f_5613_, v___x_5614_, v_x_5615_, v_x_5616_);
    return v___x_5618_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_5619_: *mut LeanObject,
    mut v_f_5620_: *mut LeanObject,
    mut v___x_5621_: *mut LeanObject,
    mut v_x_5622_: *mut LeanObject,
    mut v_x_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5625_: *mut LeanObject = core::ptr::null_mut();
    v_res_5625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__6(v_00_u03b1_5619_, v_f_5620_, v___x_5621_, v_x_5622_, v_x_5623_);
    return v_res_5625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b1_5626_: *mut LeanObject,
    mut v_f_5627_: *mut LeanObject,
    mut v___x_5628_: *mut LeanObject,
    mut v_as_5629_: *mut LeanObject,
    mut v_i_5630_: usize,
    mut v_stop_5631_: usize,
    mut v_b_5632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    v___x_5634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_f_5627_, v___x_5628_, v_as_5629_, v_i_5630_, v_stop_5631_, v_b_5632_);
    return v___x_5634_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_00_u03b1_5635_: *mut LeanObject,
    mut v_f_5636_: *mut LeanObject,
    mut v___x_5637_: *mut LeanObject,
    mut v_as_5638_: *mut LeanObject,
    mut v_i_5639_: *mut LeanObject,
    mut v_stop_5640_: *mut LeanObject,
    mut v_b_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5643_: usize = 0;
    let mut v_stop_boxed_5644_: usize = 0;
    let mut v_res_5645_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5643_ = lean_unbox_usize(v_i_5639_);
    lean_dec(v_i_5639_);
    v_stop_boxed_5644_ = lean_unbox_usize(v_stop_5640_);
    lean_dec(v_stop_5640_);
    v_res_5645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___at___00Lean_Elab_InfoTree_foldInfoM___at___00Lean_Elab_InfoTree_collectTermInfoM___at___00Lean_Linter_List_binders_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_00_u03b1_5635_, v_f_5636_, v___x_5637_, v_as_5638_, v_i_boxed_5643_, v_stop_boxed_5644_, v_b_5641_);
    lean_dec_ref(v_as_5638_);
    return v_res_5645_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    v___x_5647_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__0;
    v___x_5648_ = l_Lean_stringToMessageData(v___x_5647_);
    return v___x_5648_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(
    mut v_as_x27_5652_: *mut LeanObject,
    mut v_b_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: u8 = 0;
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: u8 = 0;
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5652_) == 0 {
                    v___x_5657_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5657_, 0, v_b_5653_);
                    return v___x_5657_;
                } else {
                    v_head_5658_ = lean_ctor_get(v_as_x27_5652_, 0);
                    v_snd_5659_ = lean_ctor_get(v_head_5658_, 1);
                    v_tail_5660_ = lean_ctor_get(v_as_x27_5652_, 1);
                    v_fst_5661_ = lean_ctor_get(v_head_5658_, 0);
                    v_fst_5662_ = lean_ctor_get(v_snd_5659_, 0);
                    v_snd_5663_ = lean_ctor_get(v_snd_5659_, 1);
                    v___x_5664_ = lean_box(0);
                    if lean_obj_tag(v_fst_5662_) == 1 {
                        v_str_5665_ = lean_ctor_get(v_fst_5662_, 1);
                        lean_inc_ref(v_str_5665_);
                        v___x_5666_ = l_Lean_Linter_List_stripBinderName(v_str_5665_);
                        v___x_5667_ = l_Lean_Linter_List_allowedArrayNames;
                        v___x_5668_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5666_,
                            v___x_5667_,
                        );
                        if v___x_5668_ == 0 {
                            v___x_5669_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5680_ = l_Lean_Expr_getAppNumArgs(v_snd_5663_);
                            v___x_5681_ = lean_unsigned_to_nat(1);
                            v___x_5682_ = lean_nat_sub(v___x_5680_, v___x_5681_);
                            lean_dec(v___x_5680_);
                            v___x_5683_ = l_Lean_Expr_getRevArg_x21(v_snd_5663_, v___x_5682_);
                            v___x_5684_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                            v___x_5685_ = l_Lean_Expr_isAppOf(v___x_5683_, v___x_5684_);
                            if v___x_5685_ == 0 {
                                v___x_5686_ =
                                    l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                                v___x_5687_ = l_Lean_Expr_isAppOf(v___x_5683_, v___x_5686_);
                                lean_dec_ref(v___x_5683_);
                                if v___x_5687_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_5683_);
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_5666_);
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
                v___x_5671_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__1);
                v___x_5672_ = l_Lean_stringToMessageData(v___x_5666_);
                v___x_5673_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5673_, 0, v___x_5671_);
                lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                v___x_5674_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5669_,
                    v_fst_5661_,
                    v___x_5673_,
                    v___y_5654_,
                    v___y_5655_,
                );
                if lean_obj_tag(v___x_5674_) == 0 {
                    lean_dec_ref_known(v___x_5674_, 1);
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
                    lean_dec_ref(v___x_5666_);
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
    mut v_as_x27_5690_: *mut LeanObject,
    mut v_b_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5695_: *mut LeanObject = core::ptr::null_mut();
    v_res_5695_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(
            v_as_x27_5690_,
            v_b_5691_,
            v___y_5692_,
            v___y_5693_,
        );
    lean_dec(v___y_5693_);
    lean_dec_ref(v___y_5692_);
    lean_dec(v_as_x27_5690_);
    return v_res_5695_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    v___x_5697_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__0;
    v___x_5698_ = l_Lean_stringToMessageData(v___x_5697_);
    return v___x_5698_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(
    mut v_as_x27_5702_: *mut LeanObject,
    mut v_b_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: u8 = 0;
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: u8 = 0;
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5702_) == 0 {
                    v___x_5707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5707_, 0, v_b_5703_);
                    return v___x_5707_;
                } else {
                    v_head_5708_ = lean_ctor_get(v_as_x27_5702_, 0);
                    v_snd_5709_ = lean_ctor_get(v_head_5708_, 1);
                    v_tail_5710_ = lean_ctor_get(v_as_x27_5702_, 1);
                    v_fst_5711_ = lean_ctor_get(v_head_5708_, 0);
                    v_fst_5712_ = lean_ctor_get(v_snd_5709_, 0);
                    v_snd_5713_ = lean_ctor_get(v_snd_5709_, 1);
                    v___x_5714_ = lean_box(0);
                    if lean_obj_tag(v_fst_5712_) == 1 {
                        v_str_5715_ = lean_ctor_get(v_fst_5712_, 1);
                        lean_inc_ref(v_str_5715_);
                        v___x_5716_ = l_Lean_Linter_List_stripBinderName(v_str_5715_);
                        v___x_5717_ = l_Lean_Linter_List_allowedListNames;
                        v___x_5718_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5716_,
                            v___x_5717_,
                        );
                        if v___x_5718_ == 0 {
                            v___x_5719_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5733_ = l_Lean_Expr_getAppNumArgs(v_snd_5713_);
                            v___x_5734_ = lean_unsigned_to_nat(1);
                            v___x_5735_ = lean_nat_sub(v___x_5733_, v___x_5734_);
                            lean_dec(v___x_5733_);
                            v___x_5736_ = l_Lean_Expr_getRevArg_x21(v_snd_5713_, v___x_5735_);
                            v___x_5737_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3;
                            v___x_5738_ = l_Lean_Expr_isAppOf(v___x_5736_, v___x_5737_);
                            if v___x_5738_ == 0 {
                                v___x_5739_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                                v___x_5740_ = l_Lean_Expr_isAppOf(v___x_5736_, v___x_5739_);
                                lean_dec_ref(v___x_5736_);
                                if v___x_5740_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_5736_);
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_5716_);
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
                v___x_5721_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__1);
                v___x_5722_ = l_Lean_stringToMessageData(v___x_5716_);
                v___x_5723_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5723_, 0, v___x_5721_);
                lean_ctor_set(v___x_5723_, 1, v___x_5722_);
                v___x_5724_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5719_,
                    v_fst_5711_,
                    v___x_5723_,
                    v___y_5704_,
                    v___y_5705_,
                );
                if lean_obj_tag(v___x_5724_) == 0 {
                    lean_dec_ref_known(v___x_5724_, 1);
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
                        lean_dec_ref(v___x_5716_);
                        v_as_x27_5702_ = v_tail_5710_;
                        v_b_5703_ = v___x_5714_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5716_);
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
    mut v_as_x27_5743_: *mut LeanObject,
    mut v_b_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5748_: *mut LeanObject = core::ptr::null_mut();
    v_res_5748_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(
            v_as_x27_5743_,
            v_b_5744_,
            v___y_5745_,
            v___y_5746_,
        );
    lean_dec(v___y_5746_);
    lean_dec_ref(v___y_5745_);
    lean_dec(v_as_x27_5743_);
    return v_res_5748_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(
    mut v_a_5749_: *mut LeanObject,
    mut v_a_5750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5757_: u8 = 0;
    let mut v_snd_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_unused_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5749_) == 0 {
                    v___x_5751_ = l_List_reverse___redArg(v_a_5750_);
                    return v___x_5751_;
                } else {
                    v_head_5752_ = lean_ctor_get(v_a_5749_, 0);
                    lean_inc(v_head_5752_);
                    v_snd_5753_ = lean_ctor_get(v_head_5752_, 1);
                    v_tail_5754_ = lean_ctor_get(v_a_5749_, 1);
                    v_isSharedCheck_5766_ = (!lean_is_exclusive(v_a_5749_)) as u8;
                    if v_isSharedCheck_5766_ == 0 {
                        v_unused_5767_ = lean_ctor_get(v_a_5749_, 0);
                        lean_dec(v_unused_5767_);
                        v___x_5756_ = v_a_5749_;
                        v_isShared_5757_ = v_isSharedCheck_5766_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5754_);
                        lean_dec(v_a_5749_);
                        v___x_5756_ = lean_box(0);
                        v_isShared_5757_ = v_isSharedCheck_5766_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5758_ = lean_ctor_get(v_snd_5753_, 1);
                v___x_5759_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg___closed__3;
                v___x_5760_ = l_Lean_Expr_isAppOf(v_snd_5758_, v___x_5759_);
                if v___x_5760_ == 0 {
                    lean_del_object(v___x_5756_);
                    lean_dec(v_head_5752_);
                    v_a_5749_ = v_tail_5754_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5757_ == 0 {
                        lean_ctor_set(v___x_5756_, 1, v_a_5750_);
                        v___x_5763_ = v___x_5756_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_head_5752_);
                        lean_ctor_set(v_reuseFailAlloc_5765_, 1, v_a_5750_);
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
    mut v_x_5769_: *mut LeanObject,
) -> u8 {
    return v___x_5768_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed(
    mut v___x_5770_: *mut LeanObject,
    mut v_x_5771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16026__boxed_5772_: u8 = 0;
    let mut v_res_5773_: u8 = 0;
    let mut v_r_5774_: *mut LeanObject = core::ptr::null_mut();
    v___x_16026__boxed_5772_ = (lean_unbox(v___x_5770_) as u8);
    v_res_5773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0(v___x_16026__boxed_5772_, v_x_5771_);
    lean_dec_ref(v_x_5771_);
    v_r_5774_ = lean_box((v_res_5773_) as usize);
    return v_r_5774_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v_snd_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut v_unused_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5775_) == 0 {
                    v___x_5777_ = l_List_reverse___redArg(v_a_5776_);
                    return v___x_5777_;
                } else {
                    v_head_5778_ = lean_ctor_get(v_a_5775_, 0);
                    lean_inc(v_head_5778_);
                    v_snd_5779_ = lean_ctor_get(v_head_5778_, 1);
                    v_tail_5780_ = lean_ctor_get(v_a_5775_, 1);
                    v_isSharedCheck_5792_ = (!lean_is_exclusive(v_a_5775_)) as u8;
                    if v_isSharedCheck_5792_ == 0 {
                        v_unused_5793_ = lean_ctor_get(v_a_5775_, 0);
                        lean_dec(v_unused_5793_);
                        v___x_5782_ = v_a_5775_;
                        v_isShared_5783_ = v_isSharedCheck_5792_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5780_);
                        lean_dec(v_a_5775_);
                        v___x_5782_ = lean_box(0);
                        v_isShared_5783_ = v_isSharedCheck_5792_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5784_ = lean_ctor_get(v_snd_5779_, 1);
                v___x_5785_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg___closed__3;
                v___x_5786_ = l_Lean_Expr_isAppOf(v_snd_5784_, v___x_5785_);
                if v___x_5786_ == 0 {
                    lean_del_object(v___x_5782_);
                    lean_dec(v_head_5778_);
                    v_a_5775_ = v_tail_5780_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5783_ == 0 {
                        lean_ctor_set(v___x_5782_, 1, v_a_5776_);
                        v___x_5789_ = v___x_5782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5791_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_head_5778_);
                        lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_a_5776_);
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
-> *mut LeanObject {
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__0;
    v___x_5796_ = l_Lean_stringToMessageData(v___x_5795_);
    return v___x_5796_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(
    mut v_as_x27_5797_: *mut LeanObject,
    mut v_b_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: u8 = 0;
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5797_) == 0 {
                    v___x_5802_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5802_, 0, v_b_5798_);
                    return v___x_5802_;
                } else {
                    v_head_5803_ = lean_ctor_get(v_as_x27_5797_, 0);
                    v_snd_5804_ = lean_ctor_get(v_head_5803_, 1);
                    v_tail_5805_ = lean_ctor_get(v_as_x27_5797_, 1);
                    v_fst_5806_ = lean_ctor_get(v_head_5803_, 0);
                    v_fst_5807_ = lean_ctor_get(v_snd_5804_, 0);
                    v_snd_5808_ = lean_ctor_get(v_snd_5804_, 1);
                    v___x_5809_ = lean_box(0);
                    if lean_obj_tag(v_fst_5807_) == 1 {
                        v_str_5810_ = lean_ctor_get(v_fst_5807_, 1);
                        lean_inc_ref(v_str_5810_);
                        v___x_5811_ = l_Lean_Linter_List_stripBinderName(v_str_5810_);
                        v___x_5812_ = l_Lean_Linter_List_allowedVectorNames;
                        v___x_5813_ = l_List_elem___at___00Lean_Linter_List_indexLinter_spec__1(
                            v___x_5811_,
                            v___x_5812_,
                        );
                        if v___x_5813_ == 0 {
                            v___x_5814_ = l_Lean_Linter_List_linter_listVariables;
                            v___x_5821_ = l_Lean_Expr_getAppNumArgs(v_snd_5808_);
                            v___x_5822_ = lean_unsigned_to_nat(1);
                            v___x_5823_ = lean_nat_sub(v___x_5821_, v___x_5822_);
                            lean_dec(v___x_5821_);
                            v___x_5824_ = l_Lean_Expr_getRevArg_x21(v_snd_5808_, v___x_5823_);
                            v___x_5825_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                            v___x_5826_ = l_Lean_Expr_isAppOf(v___x_5824_, v___x_5825_);
                            lean_dec_ref(v___x_5824_);
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
                                    lean_dec_ref(v___x_5811_);
                                    v_as_x27_5797_ = v_tail_5805_;
                                    v_b_5798_ = v___x_5809_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5811_);
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
                v___x_5816_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg___closed__1);
                v___x_5817_ = l_Lean_stringToMessageData(v___x_5811_);
                v___x_5818_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5818_, 0, v___x_5816_);
                lean_ctor_set(v___x_5818_, 1, v___x_5817_);
                v___x_5819_ = l_Lean_Linter_logLint___at___00Lean_Linter_List_indexLinter_spec__2(
                    v___x_5814_,
                    v_fst_5806_,
                    v___x_5818_,
                    v___y_5799_,
                    v___y_5800_,
                );
                if lean_obj_tag(v___x_5819_) == 0 {
                    lean_dec_ref_known(v___x_5819_, 1);
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
    mut v_as_x27_5832_: *mut LeanObject,
    mut v_b_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5837_: *mut LeanObject = core::ptr::null_mut();
    v_res_5837_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(
            v_as_x27_5832_,
            v_b_5833_,
            v___y_5834_,
            v___y_5835_,
        );
    lean_dec(v___y_5835_);
    lean_dec_ref(v___y_5834_);
    lean_dec(v_as_x27_5832_);
    return v_res_5837_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(
    mut v_a_5838_: *mut LeanObject,
    mut v_a_5839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v_snd_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_unused_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5838_) == 0 {
                    v___x_5840_ = l_List_reverse___redArg(v_a_5839_);
                    return v___x_5840_;
                } else {
                    v_head_5841_ = lean_ctor_get(v_a_5838_, 0);
                    lean_inc(v_head_5841_);
                    v_snd_5842_ = lean_ctor_get(v_head_5841_, 1);
                    v_tail_5843_ = lean_ctor_get(v_a_5838_, 1);
                    v_isSharedCheck_5855_ = (!lean_is_exclusive(v_a_5838_)) as u8;
                    if v_isSharedCheck_5855_ == 0 {
                        v_unused_5856_ = lean_ctor_get(v_a_5838_, 0);
                        lean_dec(v_unused_5856_);
                        v___x_5845_ = v_a_5838_;
                        v_isShared_5846_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5843_);
                        lean_dec(v_a_5838_);
                        v___x_5845_ = lean_box(0);
                        v_isShared_5846_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5847_ = lean_ctor_get(v_snd_5842_, 1);
                v___x_5848_ = l_Lean_Linter_List_numericalWidths___lam__1___closed__4;
                v___x_5849_ = l_Lean_Expr_isAppOf(v_snd_5847_, v___x_5848_);
                if v___x_5849_ == 0 {
                    lean_del_object(v___x_5845_);
                    lean_dec(v_head_5841_);
                    v_a_5838_ = v_tail_5843_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5846_ == 0 {
                        lean_ctor_set(v___x_5845_, 1, v_a_5839_);
                        v___x_5852_ = v___x_5845_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_head_5841_);
                        lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_a_5839_);
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
    mut v_as_5858_: *mut LeanObject,
    mut v_sz_5859_: usize,
    mut v_i_5860_: usize,
    mut v_b_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5865_: u8 = 0;
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: usize = 0;
    let mut v___x_5882_: usize = 0;
    let mut v_a_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut v_a_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5899_: u8 = 0;
    let mut v_a_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5907_: u8 = 0;
    let mut v_a_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v_ref_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5865_ = lean_usize_dec_lt(v_i_5860_, v_sz_5859_);
                if v___x_5865_ == 0 {
                    v___x_5866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5866_, 0, v_b_5861_);
                    return v___x_5866_;
                } else {
                    lean_dec_ref(v_b_5861_);
                    v___x_5867_ = lean_box((v___x_5857_) as usize);
                    v___f_5868_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_5868_, 0, v___x_5867_);
                    v_a_5869_ = lean_array_uget_borrowed(v_as_5858_, v_i_5860_);
                    lean_inc(v_a_5869_);
                    v___x_5870_ = l_Lean_Linter_List_binders(v_a_5869_, v___f_5868_);
                    if lean_obj_tag(v___x_5870_) == 0 {
                        v_a_5871_ = lean_ctor_get(v___x_5870_, 0);
                        lean_inc_n(v_a_5871_, 2);
                        lean_dec_ref_known(v___x_5870_, 1);
                        v___x_5872_ = lean_box(0);
                        v___x_5873_ = lean_box(0);
                        v___x_5874_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_5871_, v___x_5873_);
                        v___x_5875_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_5874_, v___x_5872_, v___y_5862_, v___y_5863_);
                        lean_dec(v___x_5874_);
                        if lean_obj_tag(v___x_5875_) == 0 {
                            lean_dec_ref_known(v___x_5875_, 1);
                            lean_inc(v_a_5871_);
                            v___x_5876_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_5871_, v___x_5873_);
                            v___x_5877_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_5876_, v___x_5872_, v___y_5862_, v___y_5863_);
                            lean_dec(v___x_5876_);
                            if lean_obj_tag(v___x_5877_) == 0 {
                                lean_dec_ref_known(v___x_5877_, 1);
                                v___x_5878_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_5871_, v___x_5873_);
                                v___x_5879_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_5878_, v___x_5872_, v___y_5862_, v___y_5863_);
                                lean_dec(v___x_5878_);
                                if lean_obj_tag(v___x_5879_) == 0 {
                                    lean_dec_ref_known(v___x_5879_, 1);
                                    v___x_5880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                    v___x_5881_ = 1usize;
                                    v___x_5882_ = lean_usize_add(v_i_5860_, v___x_5881_);
                                    v_i_5860_ = v___x_5882_;
                                    v_b_5861_ = v___x_5880_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_a_5884_ = lean_ctor_get(v___x_5879_, 0);
                                    v_isSharedCheck_5891_ = (!lean_is_exclusive(v___x_5879_)) as u8;
                                    if v_isSharedCheck_5891_ == 0 {
                                        v___x_5886_ = v___x_5879_;
                                        v_isShared_5887_ = v_isSharedCheck_5891_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5884_);
                                        lean_dec(v___x_5879_);
                                        v___x_5886_ = lean_box(0);
                                        v_isShared_5887_ = v_isSharedCheck_5891_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5871_);
                                v_a_5892_ = lean_ctor_get(v___x_5877_, 0);
                                v_isSharedCheck_5899_ = (!lean_is_exclusive(v___x_5877_)) as u8;
                                if v_isSharedCheck_5899_ == 0 {
                                    v___x_5894_ = v___x_5877_;
                                    v_isShared_5895_ = v_isSharedCheck_5899_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5892_);
                                    lean_dec(v___x_5877_);
                                    v___x_5894_ = lean_box(0);
                                    v_isShared_5895_ = v_isSharedCheck_5899_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5871_);
                            v_a_5900_ = lean_ctor_get(v___x_5875_, 0);
                            v_isSharedCheck_5907_ = (!lean_is_exclusive(v___x_5875_)) as u8;
                            if v_isSharedCheck_5907_ == 0 {
                                v___x_5902_ = v___x_5875_;
                                v_isShared_5903_ = v_isSharedCheck_5907_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5900_);
                                lean_dec(v___x_5875_);
                                v___x_5902_ = lean_box(0);
                                v_isShared_5903_ = v_isSharedCheck_5907_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_5908_ = lean_ctor_get(v___x_5870_, 0);
                        v_isSharedCheck_5920_ = (!lean_is_exclusive(v___x_5870_)) as u8;
                        if v_isSharedCheck_5920_ == 0 {
                            v___x_5910_ = v___x_5870_;
                            v_isShared_5911_ = v_isSharedCheck_5920_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5908_);
                            lean_dec(v___x_5870_);
                            v___x_5910_ = lean_box(0);
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
                    v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
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
                    v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
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
                    v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
                    v___x_5905_ = v_reuseFailAlloc_5906_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5905_;
            }
            7 => {
                v_ref_5912_ = lean_ctor_get(v___y_5862_, 7);
                v___x_5913_ = lean_io_error_to_string(v_a_5908_);
                v___x_5914_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5914_, 0, v___x_5913_);
                v___x_5915_ = l_Lean_MessageData_ofFormat(v___x_5914_);
                lean_inc(v_ref_5912_);
                v___x_5916_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5916_, 0, v_ref_5912_);
                lean_ctor_set(v___x_5916_, 1, v___x_5915_);
                if v_isShared_5911_ == 0 {
                    lean_ctor_set(v___x_5910_, 0, v___x_5916_);
                    v___x_5918_ = v___x_5910_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 0, v___x_5916_);
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
    mut v___x_5921_: *mut LeanObject,
    mut v_as_5922_: *mut LeanObject,
    mut v_sz_5923_: *mut LeanObject,
    mut v_i_5924_: *mut LeanObject,
    mut v_b_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
    mut v___y_5928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16206__boxed_5929_: u8 = 0;
    let mut v_sz_boxed_5930_: usize = 0;
    let mut v_i_boxed_5931_: usize = 0;
    let mut v_res_5932_: *mut LeanObject = core::ptr::null_mut();
    v___x_16206__boxed_5929_ = (lean_unbox(v___x_5921_) as u8);
    v_sz_boxed_5930_ = lean_unbox_usize(v_sz_5923_);
    lean_dec(v_sz_5923_);
    v_i_boxed_5931_ = lean_unbox_usize(v_i_5924_);
    lean_dec(v_i_5924_);
    v_res_5932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_16206__boxed_5929_, v_as_5922_, v_sz_boxed_5930_, v_i_boxed_5931_, v_b_5925_, v___y_5926_, v___y_5927_);
    lean_dec(v___y_5927_);
    lean_dec_ref(v___y_5926_);
    lean_dec_ref(v_as_5922_);
    return v_res_5932_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(
    mut v___x_5933_: u8,
    mut v_as_5934_: *mut LeanObject,
    mut v_sz_5935_: usize,
    mut v_i_5936_: usize,
    mut v_b_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5941_: u8 = 0;
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: usize = 0;
    let mut v___x_5958_: usize = 0;
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_a_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_a_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v_ref_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5941_ = lean_usize_dec_lt(v_i_5936_, v_sz_5935_);
                if v___x_5941_ == 0 {
                    v___x_5942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5942_, 0, v_b_5937_);
                    return v___x_5942_;
                } else {
                    lean_dec_ref(v_b_5937_);
                    v___x_5943_ = lean_box((v___x_5933_) as usize);
                    v___f_5944_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_5944_, 0, v___x_5943_);
                    v_a_5945_ = lean_array_uget_borrowed(v_as_5934_, v_i_5936_);
                    lean_inc(v_a_5945_);
                    v___x_5946_ = l_Lean_Linter_List_binders(v_a_5945_, v___f_5944_);
                    if lean_obj_tag(v___x_5946_) == 0 {
                        v_a_5947_ = lean_ctor_get(v___x_5946_, 0);
                        lean_inc_n(v_a_5947_, 2);
                        lean_dec_ref_known(v___x_5946_, 1);
                        v___x_5948_ = lean_box(0);
                        v___x_5949_ = lean_box(0);
                        v___x_5950_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_5947_, v___x_5949_);
                        v___x_5951_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_5950_, v___x_5948_, v___y_5938_, v___y_5939_);
                        lean_dec(v___x_5950_);
                        if lean_obj_tag(v___x_5951_) == 0 {
                            lean_dec_ref_known(v___x_5951_, 1);
                            lean_inc(v_a_5947_);
                            v___x_5952_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_5947_, v___x_5949_);
                            v___x_5953_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_5952_, v___x_5948_, v___y_5938_, v___y_5939_);
                            lean_dec(v___x_5952_);
                            if lean_obj_tag(v___x_5953_) == 0 {
                                lean_dec_ref_known(v___x_5953_, 1);
                                v___x_5954_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_5947_, v___x_5949_);
                                v___x_5955_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_5954_, v___x_5948_, v___y_5938_, v___y_5939_);
                                lean_dec(v___x_5954_);
                                if lean_obj_tag(v___x_5955_) == 0 {
                                    lean_dec_ref_known(v___x_5955_, 1);
                                    v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__7_spec__10_spec__13___closed__0;
                                    v___x_5957_ = 1usize;
                                    v___x_5958_ = lean_usize_add(v_i_5936_, v___x_5957_);
                                    v___x_5959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8_spec__9(v___x_5933_, v_as_5934_, v_sz_5935_, v___x_5958_, v___x_5956_, v___y_5938_, v___y_5939_);
                                    return v___x_5959_;
                                } else {
                                    v_a_5960_ = lean_ctor_get(v___x_5955_, 0);
                                    v_isSharedCheck_5967_ = (!lean_is_exclusive(v___x_5955_)) as u8;
                                    if v_isSharedCheck_5967_ == 0 {
                                        v___x_5962_ = v___x_5955_;
                                        v_isShared_5963_ = v_isSharedCheck_5967_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5960_);
                                        lean_dec(v___x_5955_);
                                        v___x_5962_ = lean_box(0);
                                        v_isShared_5963_ = v_isSharedCheck_5967_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5947_);
                                v_a_5968_ = lean_ctor_get(v___x_5953_, 0);
                                v_isSharedCheck_5975_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                                if v_isSharedCheck_5975_ == 0 {
                                    v___x_5970_ = v___x_5953_;
                                    v_isShared_5971_ = v_isSharedCheck_5975_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5968_);
                                    lean_dec(v___x_5953_);
                                    v___x_5970_ = lean_box(0);
                                    v_isShared_5971_ = v_isSharedCheck_5975_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5947_);
                            v_a_5976_ = lean_ctor_get(v___x_5951_, 0);
                            v_isSharedCheck_5983_ = (!lean_is_exclusive(v___x_5951_)) as u8;
                            if v_isSharedCheck_5983_ == 0 {
                                v___x_5978_ = v___x_5951_;
                                v_isShared_5979_ = v_isSharedCheck_5983_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5976_);
                                lean_dec(v___x_5951_);
                                v___x_5978_ = lean_box(0);
                                v_isShared_5979_ = v_isSharedCheck_5983_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_5984_ = lean_ctor_get(v___x_5946_, 0);
                        v_isSharedCheck_5996_ = (!lean_is_exclusive(v___x_5946_)) as u8;
                        if v_isSharedCheck_5996_ == 0 {
                            v___x_5986_ = v___x_5946_;
                            v_isShared_5987_ = v_isSharedCheck_5996_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5984_);
                            lean_dec(v___x_5946_);
                            v___x_5986_ = lean_box(0);
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
                    v_reuseFailAlloc_5966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_a_5960_);
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
                    v_reuseFailAlloc_5974_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_a_5968_);
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
                    v_reuseFailAlloc_5982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5976_);
                    v___x_5981_ = v_reuseFailAlloc_5982_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5981_;
            }
            7 => {
                v_ref_5988_ = lean_ctor_get(v___y_5938_, 7);
                v___x_5989_ = lean_io_error_to_string(v_a_5984_);
                v___x_5990_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5990_, 0, v___x_5989_);
                v___x_5991_ = l_Lean_MessageData_ofFormat(v___x_5990_);
                lean_inc(v_ref_5988_);
                v___x_5992_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5992_, 0, v_ref_5988_);
                lean_ctor_set(v___x_5992_, 1, v___x_5991_);
                if v_isShared_5987_ == 0 {
                    lean_ctor_set(v___x_5986_, 0, v___x_5992_);
                    v___x_5994_ = v___x_5986_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5992_);
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
    mut v___x_5997_: *mut LeanObject,
    mut v_as_5998_: *mut LeanObject,
    mut v_sz_5999_: *mut LeanObject,
    mut v_i_6000_: *mut LeanObject,
    mut v_b_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16333__boxed_6005_: u8 = 0;
    let mut v_sz_boxed_6006_: usize = 0;
    let mut v_i_boxed_6007_: usize = 0;
    let mut v_res_6008_: *mut LeanObject = core::ptr::null_mut();
    v___x_16333__boxed_6005_ = (lean_unbox(v___x_5997_) as u8);
    v_sz_boxed_6006_ = lean_unbox_usize(v_sz_5999_);
    lean_dec(v_sz_5999_);
    v_i_boxed_6007_ = lean_unbox_usize(v_i_6000_);
    lean_dec(v_i_6000_);
    v_res_6008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_16333__boxed_6005_, v_as_5998_, v_sz_boxed_6006_, v_i_boxed_6007_, v_b_6001_, v___y_6002_, v___y_6003_);
    lean_dec(v___y_6003_);
    lean_dec_ref(v___y_6002_);
    lean_dec_ref(v_as_5998_);
    return v_res_6008_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(
    mut v_init_6009_: *mut LeanObject,
    mut v___x_6010_: u8,
    mut v_n_6011_: *mut LeanObject,
    mut v_b_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6019_: usize = 0;
    let mut v___x_6020_: usize = 0;
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6025_: u8 = 0;
    let mut v_fst_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_a_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v_vs_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6048_: usize = 0;
    let mut v___x_6049_: usize = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v_fst_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6011_) == 0 {
                    v_cs_6016_ = lean_ctor_get(v_n_6011_, 0);
                    v___x_6017_ = lean_box(0);
                    v___x_6018_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6018_, 0, v___x_6017_);
                    lean_ctor_set(v___x_6018_, 1, v_b_6012_);
                    v_sz_6019_ = lean_array_size(v_cs_6016_);
                    v___x_6020_ = 0usize;
                    v___x_6021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_6009_, v___x_6010_, v_cs_6016_, v_sz_6019_, v___x_6020_, v___x_6018_, v___y_6013_, v___y_6014_);
                    if lean_obj_tag(v___x_6021_) == 0 {
                        v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
                        v_isSharedCheck_6036_ = (!lean_is_exclusive(v___x_6021_)) as u8;
                        if v_isSharedCheck_6036_ == 0 {
                            v___x_6024_ = v___x_6021_;
                            v_isShared_6025_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6022_);
                            lean_dec(v___x_6021_);
                            v___x_6024_ = lean_box(0);
                            v_isShared_6025_ = v_isSharedCheck_6036_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6037_ = lean_ctor_get(v___x_6021_, 0);
                        v_isSharedCheck_6044_ = (!lean_is_exclusive(v___x_6021_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6039_ = v___x_6021_;
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6037_);
                            lean_dec(v___x_6021_);
                            v___x_6039_ = lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6045_ = lean_ctor_get(v_n_6011_, 0);
                    v___x_6046_ = lean_box(0);
                    v___x_6047_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6047_, 0, v___x_6046_);
                    lean_ctor_set(v___x_6047_, 1, v_b_6012_);
                    v_sz_6048_ = lean_array_size(v_vs_6045_);
                    v___x_6049_ = 0usize;
                    v___x_6050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__8(v___x_6010_, v_vs_6045_, v_sz_6048_, v___x_6049_, v___x_6047_, v___y_6013_, v___y_6014_);
                    if lean_obj_tag(v___x_6050_) == 0 {
                        v_a_6051_ = lean_ctor_get(v___x_6050_, 0);
                        v_isSharedCheck_6065_ = (!lean_is_exclusive(v___x_6050_)) as u8;
                        if v_isSharedCheck_6065_ == 0 {
                            v___x_6053_ = v___x_6050_;
                            v_isShared_6054_ = v_isSharedCheck_6065_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6051_);
                            lean_dec(v___x_6050_);
                            v___x_6053_ = lean_box(0);
                            v_isShared_6054_ = v_isSharedCheck_6065_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6066_ = lean_ctor_get(v___x_6050_, 0);
                        v_isSharedCheck_6073_ = (!lean_is_exclusive(v___x_6050_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6050_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6066_);
                            lean_dec(v___x_6050_);
                            v___x_6068_ = lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6026_ = lean_ctor_get(v_a_6022_, 0);
                if lean_obj_tag(v_fst_6026_) == 0 {
                    v_snd_6027_ = lean_ctor_get(v_a_6022_, 1);
                    lean_inc(v_snd_6027_);
                    lean_dec(v_a_6022_);
                    v___x_6028_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6028_, 0, v_snd_6027_);
                    if v_isShared_6025_ == 0 {
                        lean_ctor_set(v___x_6024_, 0, v___x_6028_);
                        v___x_6030_ = v___x_6024_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6028_);
                        v___x_6030_ = v_reuseFailAlloc_6031_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6026_);
                    lean_dec(v_a_6022_);
                    v_val_6032_ = lean_ctor_get(v_fst_6026_, 0);
                    lean_inc(v_val_6032_);
                    lean_dec_ref_known(v_fst_6026_, 1);
                    if v_isShared_6025_ == 0 {
                        lean_ctor_set(v___x_6024_, 0, v_val_6032_);
                        v___x_6034_ = v___x_6024_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_val_6032_);
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
                    v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6042_;
            }
            6 => {
                v_fst_6055_ = lean_ctor_get(v_a_6051_, 0);
                if lean_obj_tag(v_fst_6055_) == 0 {
                    v_snd_6056_ = lean_ctor_get(v_a_6051_, 1);
                    lean_inc(v_snd_6056_);
                    lean_dec(v_a_6051_);
                    v___x_6057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6057_, 0, v_snd_6056_);
                    if v_isShared_6054_ == 0 {
                        lean_ctor_set(v___x_6053_, 0, v___x_6057_);
                        v___x_6059_ = v___x_6053_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6060_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6060_, 0, v___x_6057_);
                        v___x_6059_ = v_reuseFailAlloc_6060_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6055_);
                    lean_dec(v_a_6051_);
                    v_val_6061_ = lean_ctor_get(v_fst_6055_, 0);
                    lean_inc(v_val_6061_);
                    lean_dec_ref_known(v_fst_6055_, 1);
                    if v_isShared_6054_ == 0 {
                        lean_ctor_set(v___x_6053_, 0, v_val_6061_);
                        v___x_6063_ = v___x_6053_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_val_6061_);
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
                    v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
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
    mut v_init_6074_: *mut LeanObject,
    mut v___x_6075_: u8,
    mut v_as_6076_: *mut LeanObject,
    mut v_sz_6077_: usize,
    mut v_i_6078_: usize,
    mut v_b_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6083_: u8 = 0;
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6088_: u8 = 0;
    let mut v_a_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: usize = 0;
    let mut v_reuseFailAlloc_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6110_: u8 = 0;
    let mut v_a_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6118_: u8 = 0;
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6083_ = lean_usize_dec_lt(v_i_6078_, v_sz_6077_);
                if v___x_6083_ == 0 {
                    v___x_6084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6084_, 0, v_b_6079_);
                    return v___x_6084_;
                } else {
                    v_snd_6085_ = lean_ctor_get(v_b_6079_, 1);
                    v_isSharedCheck_6119_ = (!lean_is_exclusive(v_b_6079_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v_unused_6120_ = lean_ctor_get(v_b_6079_, 0);
                        lean_dec(v_unused_6120_);
                        v___x_6087_ = v_b_6079_;
                        v_isShared_6088_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6085_);
                        lean_dec(v_b_6079_);
                        v___x_6087_ = lean_box(0);
                        v_isShared_6088_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6089_ = lean_array_uget_borrowed(v_as_6076_, v_i_6078_);
                lean_inc(v_snd_6085_);
                v___x_6090_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6074_, v___x_6075_, v_a_6089_, v_snd_6085_, v___y_6080_, v___y_6081_);
                if lean_obj_tag(v___x_6090_) == 0 {
                    v_a_6091_ = lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6110_ = (!lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6110_ == 0 {
                        v___x_6093_ = v___x_6090_;
                        v_isShared_6094_ = v_isSharedCheck_6110_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6091_);
                        lean_dec(v___x_6090_);
                        v___x_6093_ = lean_box(0);
                        v_isShared_6094_ = v_isSharedCheck_6110_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6087_);
                    lean_dec(v_snd_6085_);
                    v_a_6111_ = lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6118_ = (!lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6118_ == 0 {
                        v___x_6113_ = v___x_6090_;
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6111_);
                        lean_dec(v___x_6090_);
                        v___x_6113_ = lean_box(0);
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6091_) == 0 {
                    v___x_6095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6095_, 0, v_a_6091_);
                    if v_isShared_6088_ == 0 {
                        lean_ctor_set(v___x_6087_, 0, v___x_6095_);
                        v___x_6097_ = v___x_6087_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6095_);
                        lean_ctor_set(v_reuseFailAlloc_6101_, 1, v_snd_6085_);
                        v___x_6097_ = v_reuseFailAlloc_6101_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6093_);
                    lean_dec(v_snd_6085_);
                    v_a_6102_ = lean_ctor_get(v_a_6091_, 0);
                    lean_inc(v_a_6102_);
                    lean_dec_ref_known(v_a_6091_, 1);
                    v___x_6103_ = lean_box(0);
                    if v_isShared_6088_ == 0 {
                        lean_ctor_set(v___x_6087_, 1, v_a_6102_);
                        lean_ctor_set(v___x_6087_, 0, v___x_6103_);
                        v___x_6105_ = v___x_6087_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6109_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6109_, 0, v___x_6103_);
                        lean_ctor_set(v_reuseFailAlloc_6109_, 1, v_a_6102_);
                        v___x_6105_ = v_reuseFailAlloc_6109_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6094_ == 0 {
                    lean_ctor_set(v___x_6093_, 0, v___x_6097_);
                    v___x_6099_ = v___x_6093_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6097_);
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
                    v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
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
    mut v_init_6121_: *mut LeanObject,
    mut v___x_6122_: *mut LeanObject,
    mut v_as_6123_: *mut LeanObject,
    mut v_sz_6124_: *mut LeanObject,
    mut v_i_6125_: *mut LeanObject,
    mut v_b_6126_: *mut LeanObject,
    mut v___y_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16457__boxed_6130_: u8 = 0;
    let mut v_sz_boxed_6131_: usize = 0;
    let mut v_i_boxed_6132_: usize = 0;
    let mut v_res_6133_: *mut LeanObject = core::ptr::null_mut();
    v___x_16457__boxed_6130_ = (lean_unbox(v___x_6122_) as u8);
    v_sz_boxed_6131_ = lean_unbox_usize(v_sz_6124_);
    lean_dec(v_sz_6124_);
    v_i_boxed_6132_ = lean_unbox_usize(v_i_6125_);
    lean_dec(v_i_6125_);
    v_res_6133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6_spec__7(v_init_6121_, v___x_16457__boxed_6130_, v_as_6123_, v_sz_boxed_6131_, v_i_boxed_6132_, v_b_6126_, v___y_6127_, v___y_6128_);
    lean_dec(v___y_6128_);
    lean_dec_ref(v___y_6127_);
    lean_dec_ref(v_as_6123_);
    return v_res_6133_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6___boxed(
    mut v_init_6134_: *mut LeanObject,
    mut v___x_6135_: *mut LeanObject,
    mut v_n_6136_: *mut LeanObject,
    mut v_b_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16477__boxed_6141_: u8 = 0;
    let mut v_res_6142_: *mut LeanObject = core::ptr::null_mut();
    v___x_16477__boxed_6141_ = (lean_unbox(v___x_6135_) as u8);
    v_res_6142_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6134_, v___x_16477__boxed_6141_, v_n_6136_, v_b_6137_, v___y_6138_, v___y_6139_);
    lean_dec(v___y_6139_);
    lean_dec_ref(v___y_6138_);
    lean_dec_ref(v_n_6136_);
    return v_res_6142_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(
    mut v___x_6143_: u8,
    mut v_as_6144_: *mut LeanObject,
    mut v_sz_6145_: usize,
    mut v_i_6146_: usize,
    mut v_b_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: usize = 0;
    let mut v___x_6168_: usize = 0;
    let mut v_a_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6173_: u8 = 0;
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6177_: u8 = 0;
    let mut v_a_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6181_: u8 = 0;
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_a_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut v_a_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v_ref_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6151_ = lean_usize_dec_lt(v_i_6146_, v_sz_6145_);
                if v___x_6151_ == 0 {
                    v___x_6152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6152_, 0, v_b_6147_);
                    return v___x_6152_;
                } else {
                    lean_dec_ref(v_b_6147_);
                    v___x_6153_ = lean_box((v___x_6143_) as usize);
                    v___f_6154_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_6154_, 0, v___x_6153_);
                    v_a_6155_ = lean_array_uget_borrowed(v_as_6144_, v_i_6146_);
                    lean_inc(v_a_6155_);
                    v___x_6156_ = l_Lean_Linter_List_binders(v_a_6155_, v___f_6154_);
                    if lean_obj_tag(v___x_6156_) == 0 {
                        v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
                        lean_inc_n(v_a_6157_, 2);
                        lean_dec_ref_known(v___x_6156_, 1);
                        v___x_6158_ = lean_box(0);
                        v___x_6159_ = lean_box(0);
                        v___x_6160_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_6157_, v___x_6159_);
                        v___x_6161_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_6160_, v___x_6158_, v___y_6148_, v___y_6149_);
                        lean_dec(v___x_6160_);
                        if lean_obj_tag(v___x_6161_) == 0 {
                            lean_dec_ref_known(v___x_6161_, 1);
                            lean_inc(v_a_6157_);
                            v___x_6162_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_6157_, v___x_6159_);
                            v___x_6163_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_6162_, v___x_6158_, v___y_6148_, v___y_6149_);
                            lean_dec(v___x_6162_);
                            if lean_obj_tag(v___x_6163_) == 0 {
                                lean_dec_ref_known(v___x_6163_, 1);
                                v___x_6164_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_6157_, v___x_6159_);
                                v___x_6165_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_6164_, v___x_6158_, v___y_6148_, v___y_6149_);
                                lean_dec(v___x_6164_);
                                if lean_obj_tag(v___x_6165_) == 0 {
                                    lean_dec_ref_known(v___x_6165_, 1);
                                    v___x_6166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                    v___x_6167_ = 1usize;
                                    v___x_6168_ = lean_usize_add(v_i_6146_, v___x_6167_);
                                    v_i_6146_ = v___x_6168_;
                                    v_b_6147_ = v___x_6166_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_a_6170_ = lean_ctor_get(v___x_6165_, 0);
                                    v_isSharedCheck_6177_ = (!lean_is_exclusive(v___x_6165_)) as u8;
                                    if v_isSharedCheck_6177_ == 0 {
                                        v___x_6172_ = v___x_6165_;
                                        v_isShared_6173_ = v_isSharedCheck_6177_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6170_);
                                        lean_dec(v___x_6165_);
                                        v___x_6172_ = lean_box(0);
                                        v_isShared_6173_ = v_isSharedCheck_6177_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6157_);
                                v_a_6178_ = lean_ctor_get(v___x_6163_, 0);
                                v_isSharedCheck_6185_ = (!lean_is_exclusive(v___x_6163_)) as u8;
                                if v_isSharedCheck_6185_ == 0 {
                                    v___x_6180_ = v___x_6163_;
                                    v_isShared_6181_ = v_isSharedCheck_6185_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6178_);
                                    lean_dec(v___x_6163_);
                                    v___x_6180_ = lean_box(0);
                                    v_isShared_6181_ = v_isSharedCheck_6185_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6157_);
                            v_a_6186_ = lean_ctor_get(v___x_6161_, 0);
                            v_isSharedCheck_6193_ = (!lean_is_exclusive(v___x_6161_)) as u8;
                            if v_isSharedCheck_6193_ == 0 {
                                v___x_6188_ = v___x_6161_;
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6186_);
                                lean_dec(v___x_6161_);
                                v___x_6188_ = lean_box(0);
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_6194_ = lean_ctor_get(v___x_6156_, 0);
                        v_isSharedCheck_6206_ = (!lean_is_exclusive(v___x_6156_)) as u8;
                        if v_isSharedCheck_6206_ == 0 {
                            v___x_6196_ = v___x_6156_;
                            v_isShared_6197_ = v_isSharedCheck_6206_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6194_);
                            lean_dec(v___x_6156_);
                            v___x_6196_ = lean_box(0);
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
                    v_reuseFailAlloc_6176_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
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
                    v_reuseFailAlloc_6184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6178_);
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
                    v_reuseFailAlloc_6192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6191_;
            }
            7 => {
                v_ref_6198_ = lean_ctor_get(v___y_6148_, 7);
                v___x_6199_ = lean_io_error_to_string(v_a_6194_);
                v___x_6200_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6200_, 0, v___x_6199_);
                v___x_6201_ = l_Lean_MessageData_ofFormat(v___x_6200_);
                lean_inc(v_ref_6198_);
                v___x_6202_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6202_, 0, v_ref_6198_);
                lean_ctor_set(v___x_6202_, 1, v___x_6201_);
                if v_isShared_6197_ == 0 {
                    lean_ctor_set(v___x_6196_, 0, v___x_6202_);
                    v___x_6204_ = v___x_6196_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6205_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6205_, 0, v___x_6202_);
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
    mut v___x_6207_: *mut LeanObject,
    mut v_as_6208_: *mut LeanObject,
    mut v_sz_6209_: *mut LeanObject,
    mut v_i_6210_: *mut LeanObject,
    mut v_b_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
    mut v___y_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16661__boxed_6215_: u8 = 0;
    let mut v_sz_boxed_6216_: usize = 0;
    let mut v_i_boxed_6217_: usize = 0;
    let mut v_res_6218_: *mut LeanObject = core::ptr::null_mut();
    v___x_16661__boxed_6215_ = (lean_unbox(v___x_6207_) as u8);
    v_sz_boxed_6216_ = lean_unbox_usize(v_sz_6209_);
    lean_dec(v_sz_6209_);
    v_i_boxed_6217_ = lean_unbox_usize(v_i_6210_);
    lean_dec(v_i_6210_);
    v_res_6218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_16661__boxed_6215_, v_as_6208_, v_sz_boxed_6216_, v_i_boxed_6217_, v_b_6211_, v___y_6212_, v___y_6213_);
    lean_dec(v___y_6213_);
    lean_dec_ref(v___y_6212_);
    lean_dec_ref(v_as_6208_);
    return v_res_6218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(
    mut v___x_6219_: u8,
    mut v_as_6220_: *mut LeanObject,
    mut v_sz_6221_: usize,
    mut v_i_6222_: usize,
    mut v_b_6223_: *mut LeanObject,
    mut v___y_6224_: *mut LeanObject,
    mut v___y_6225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6227_: u8 = 0;
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: usize = 0;
    let mut v___x_6244_: usize = 0;
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6249_: u8 = 0;
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_a_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_a_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_a_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v_ref_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6227_ = lean_usize_dec_lt(v_i_6222_, v_sz_6221_);
                if v___x_6227_ == 0 {
                    v___x_6228_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6228_, 0, v_b_6223_);
                    return v___x_6228_;
                } else {
                    lean_dec_ref(v_b_6223_);
                    v___x_6229_ = lean_box((v___x_6219_) as usize);
                    v___f_6230_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_6230_, 0, v___x_6229_);
                    v_a_6231_ = lean_array_uget_borrowed(v_as_6220_, v_i_6222_);
                    lean_inc(v_a_6231_);
                    v___x_6232_ = l_Lean_Linter_List_binders(v_a_6231_, v___f_6230_);
                    if lean_obj_tag(v___x_6232_) == 0 {
                        v_a_6233_ = lean_ctor_get(v___x_6232_, 0);
                        lean_inc_n(v_a_6233_, 2);
                        lean_dec_ref_known(v___x_6232_, 1);
                        v___x_6234_ = lean_box(0);
                        v___x_6235_ = lean_box(0);
                        v___x_6236_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__0(v_a_6233_, v___x_6235_);
                        v___x_6237_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1___redArg(v___x_6236_, v___x_6234_, v___y_6224_, v___y_6225_);
                        lean_dec(v___x_6236_);
                        if lean_obj_tag(v___x_6237_) == 0 {
                            lean_dec_ref_known(v___x_6237_, 1);
                            lean_inc(v_a_6233_);
                            v___x_6238_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__2(v_a_6233_, v___x_6235_);
                            v___x_6239_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3___redArg(v___x_6238_, v___x_6234_, v___y_6224_, v___y_6225_);
                            lean_dec(v___x_6238_);
                            if lean_obj_tag(v___x_6239_) == 0 {
                                lean_dec_ref_known(v___x_6239_, 1);
                                v___x_6240_ = l_List_filterTR_loop___at___00Lean_Linter_List_listVariablesLinter_spec__4(v_a_6233_, v___x_6235_);
                                v___x_6241_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5___redArg(v___x_6240_, v___x_6234_, v___y_6224_, v___y_6225_);
                                lean_dec(v___x_6240_);
                                if lean_obj_tag(v___x_6241_) == 0 {
                                    lean_dec_ref_known(v___x_6241_, 1);
                                    v___x_6242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_indexLinter_spec__6_spec__8_spec__12___closed__0;
                                    v___x_6243_ = 1usize;
                                    v___x_6244_ = lean_usize_add(v_i_6222_, v___x_6243_);
                                    v___x_6245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7_spec__10(v___x_6219_, v_as_6220_, v_sz_6221_, v___x_6244_, v___x_6242_, v___y_6224_, v___y_6225_);
                                    return v___x_6245_;
                                } else {
                                    v_a_6246_ = lean_ctor_get(v___x_6241_, 0);
                                    v_isSharedCheck_6253_ = (!lean_is_exclusive(v___x_6241_)) as u8;
                                    if v_isSharedCheck_6253_ == 0 {
                                        v___x_6248_ = v___x_6241_;
                                        v_isShared_6249_ = v_isSharedCheck_6253_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6246_);
                                        lean_dec(v___x_6241_);
                                        v___x_6248_ = lean_box(0);
                                        v_isShared_6249_ = v_isSharedCheck_6253_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6233_);
                                v_a_6254_ = lean_ctor_get(v___x_6239_, 0);
                                v_isSharedCheck_6261_ = (!lean_is_exclusive(v___x_6239_)) as u8;
                                if v_isSharedCheck_6261_ == 0 {
                                    v___x_6256_ = v___x_6239_;
                                    v_isShared_6257_ = v_isSharedCheck_6261_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6254_);
                                    lean_dec(v___x_6239_);
                                    v___x_6256_ = lean_box(0);
                                    v_isShared_6257_ = v_isSharedCheck_6261_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6233_);
                            v_a_6262_ = lean_ctor_get(v___x_6237_, 0);
                            v_isSharedCheck_6269_ = (!lean_is_exclusive(v___x_6237_)) as u8;
                            if v_isSharedCheck_6269_ == 0 {
                                v___x_6264_ = v___x_6237_;
                                v_isShared_6265_ = v_isSharedCheck_6269_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6262_);
                                lean_dec(v___x_6237_);
                                v___x_6264_ = lean_box(0);
                                v_isShared_6265_ = v_isSharedCheck_6269_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_6270_ = lean_ctor_get(v___x_6232_, 0);
                        v_isSharedCheck_6282_ = (!lean_is_exclusive(v___x_6232_)) as u8;
                        if v_isSharedCheck_6282_ == 0 {
                            v___x_6272_ = v___x_6232_;
                            v_isShared_6273_ = v_isSharedCheck_6282_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6270_);
                            lean_dec(v___x_6232_);
                            v___x_6272_ = lean_box(0);
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
                    v_reuseFailAlloc_6252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_a_6246_);
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
                    v_reuseFailAlloc_6260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6254_);
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
                    v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6267_;
            }
            7 => {
                v_ref_6274_ = lean_ctor_get(v___y_6224_, 7);
                v___x_6275_ = lean_io_error_to_string(v_a_6270_);
                v___x_6276_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                v___x_6277_ = l_Lean_MessageData_ofFormat(v___x_6276_);
                lean_inc(v_ref_6274_);
                v___x_6278_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6278_, 0, v_ref_6274_);
                lean_ctor_set(v___x_6278_, 1, v___x_6277_);
                if v_isShared_6273_ == 0 {
                    lean_ctor_set(v___x_6272_, 0, v___x_6278_);
                    v___x_6280_ = v___x_6272_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6281_, 0, v___x_6278_);
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
    mut v___x_6283_: *mut LeanObject,
    mut v_as_6284_: *mut LeanObject,
    mut v_sz_6285_: *mut LeanObject,
    mut v_i_6286_: *mut LeanObject,
    mut v_b_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
    mut v___y_6290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16788__boxed_6291_: u8 = 0;
    let mut v_sz_boxed_6292_: usize = 0;
    let mut v_i_boxed_6293_: usize = 0;
    let mut v_res_6294_: *mut LeanObject = core::ptr::null_mut();
    v___x_16788__boxed_6291_ = (lean_unbox(v___x_6283_) as u8);
    v_sz_boxed_6292_ = lean_unbox_usize(v_sz_6285_);
    lean_dec(v_sz_6285_);
    v_i_boxed_6293_ = lean_unbox_usize(v_i_6286_);
    lean_dec(v_i_6286_);
    v_res_6294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_16788__boxed_6291_, v_as_6284_, v_sz_boxed_6292_, v_i_boxed_6293_, v_b_6287_, v___y_6288_, v___y_6289_);
    lean_dec(v___y_6289_);
    lean_dec_ref(v___y_6288_);
    lean_dec_ref(v_as_6284_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(
    mut v___x_6295_: u8,
    mut v_t_6296_: *mut LeanObject,
    mut v_init_6297_: *mut LeanObject,
    mut v___y_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v_a_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6315_: usize = 0;
    let mut v___x_6316_: usize = 0;
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6321_: u8 = 0;
    let mut v_fst_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v_a_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6335_: u8 = 0;
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6339_: u8 = 0;
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_a_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6344_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6301_ = lean_ctor_get(v_t_6296_, 0);
                v_tail_6302_ = lean_ctor_get(v_t_6296_, 1);
                v___x_6303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__6(v_init_6297_, v___x_6295_, v_root_6301_, v_init_6297_, v___y_6298_, v___y_6299_);
                if lean_obj_tag(v___x_6303_) == 0 {
                    v_a_6304_ = lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6340_ = (!lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6340_ == 0 {
                        v___x_6306_ = v___x_6303_;
                        v_isShared_6307_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6304_);
                        lean_dec(v___x_6303_);
                        v___x_6306_ = lean_box(0);
                        v_isShared_6307_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6341_ = lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6348_ = (!lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6348_ == 0 {
                        v___x_6343_ = v___x_6303_;
                        v_isShared_6344_ = v_isSharedCheck_6348_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6341_);
                        lean_dec(v___x_6303_);
                        v___x_6343_ = lean_box(0);
                        v_isShared_6344_ = v_isSharedCheck_6348_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6304_) == 0 {
                    v_a_6308_ = lean_ctor_get(v_a_6304_, 0);
                    lean_inc(v_a_6308_);
                    lean_dec_ref_known(v_a_6304_, 1);
                    if v_isShared_6307_ == 0 {
                        lean_ctor_set(v___x_6306_, 0, v_a_6308_);
                        v___x_6310_ = v___x_6306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6311_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_a_6308_);
                        v___x_6310_ = v_reuseFailAlloc_6311_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6306_);
                    v_a_6312_ = lean_ctor_get(v_a_6304_, 0);
                    lean_inc(v_a_6312_);
                    lean_dec_ref_known(v_a_6304_, 1);
                    v___x_6313_ = lean_box(0);
                    v___x_6314_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6314_, 0, v___x_6313_);
                    lean_ctor_set(v___x_6314_, 1, v_a_6312_);
                    v_sz_6315_ = lean_array_size(v_tail_6302_);
                    v___x_6316_ = 0usize;
                    v___x_6317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6_spec__7(v___x_6295_, v_tail_6302_, v_sz_6315_, v___x_6316_, v___x_6314_, v___y_6298_, v___y_6299_);
                    if lean_obj_tag(v___x_6317_) == 0 {
                        v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
                        v_isSharedCheck_6331_ = (!lean_is_exclusive(v___x_6317_)) as u8;
                        if v_isSharedCheck_6331_ == 0 {
                            v___x_6320_ = v___x_6317_;
                            v_isShared_6321_ = v_isSharedCheck_6331_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6318_);
                            lean_dec(v___x_6317_);
                            v___x_6320_ = lean_box(0);
                            v_isShared_6321_ = v_isSharedCheck_6331_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6332_ = lean_ctor_get(v___x_6317_, 0);
                        v_isSharedCheck_6339_ = (!lean_is_exclusive(v___x_6317_)) as u8;
                        if v_isSharedCheck_6339_ == 0 {
                            v___x_6334_ = v___x_6317_;
                            v_isShared_6335_ = v_isSharedCheck_6339_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6332_);
                            lean_dec(v___x_6317_);
                            v___x_6334_ = lean_box(0);
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
                v_fst_6322_ = lean_ctor_get(v_a_6318_, 0);
                if lean_obj_tag(v_fst_6322_) == 0 {
                    v_snd_6323_ = lean_ctor_get(v_a_6318_, 1);
                    lean_inc(v_snd_6323_);
                    lean_dec(v_a_6318_);
                    if v_isShared_6321_ == 0 {
                        lean_ctor_set(v___x_6320_, 0, v_snd_6323_);
                        v___x_6325_ = v___x_6320_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_snd_6323_);
                        v___x_6325_ = v_reuseFailAlloc_6326_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6322_);
                    lean_dec(v_a_6318_);
                    v_val_6327_ = lean_ctor_get(v_fst_6322_, 0);
                    lean_inc(v_val_6327_);
                    lean_dec_ref_known(v_fst_6322_, 1);
                    if v_isShared_6321_ == 0 {
                        lean_ctor_set(v___x_6320_, 0, v_val_6327_);
                        v___x_6329_ = v___x_6320_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_val_6327_);
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
                    v_reuseFailAlloc_6338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_a_6332_);
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
                    v_reuseFailAlloc_6347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_a_6341_);
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
    mut v___x_6349_: *mut LeanObject,
    mut v_t_6350_: *mut LeanObject,
    mut v_init_6351_: *mut LeanObject,
    mut v___y_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
    mut v___y_6354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16912__boxed_6355_: u8 = 0;
    let mut v_res_6356_: *mut LeanObject = core::ptr::null_mut();
    v___x_16912__boxed_6355_ = (lean_unbox(v___x_6349_) as u8);
    v_res_6356_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(
            v___x_16912__boxed_6355_,
            v_t_6350_,
            v_init_6351_,
            v___y_6352_,
            v___y_6353_,
        );
    lean_dec(v___y_6353_);
    lean_dec_ref(v___y_6352_);
    lean_dec_ref(v_t_6350_);
    return v_res_6356_;
}
pub unsafe fn l_Lean_Linter_List_listVariablesLinter___lam__0(
    mut v_stx_6357_: *mut LeanObject,
    mut v___y_6358_: *mut LeanObject,
    mut v___y_6359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v_v_6377_: u8 = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6388_: u8 = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v_unused_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6361_ = lean_st_ref_get(v___y_6359_);
                v_scopes_6365_ = lean_ctor_get(v___x_6361_, 2);
                lean_inc(v_scopes_6365_);
                lean_dec(v___x_6361_);
                v___x_6366_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_6367_ = l_List_head_x21___redArg(v___x_6366_, v_scopes_6365_);
                lean_dec(v_scopes_6365_);
                v_opts_6368_ = lean_ctor_get(v___x_6367_, 1);
                lean_inc_ref(v_opts_6368_);
                lean_dec(v___x_6367_);
                v___x_6369_ = l_Lean_Linter_List_linter_listVariables;
                v_name_6370_ = lean_ctor_get(v___x_6369_, 0);
                v_map_6371_ = lean_ctor_get(v_opts_6368_, 0);
                lean_inc(v_map_6371_);
                lean_dec_ref(v_opts_6368_);
                v___x_6372_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6371_, v_name_6370_);
                lean_dec(v_map_6371_);
                if lean_obj_tag(v___x_6372_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_6373_ = lean_ctor_get(v___x_6372_, 0);
                    v_isSharedCheck_6405_ = (!lean_is_exclusive(v___x_6372_)) as u8;
                    if v_isSharedCheck_6405_ == 0 {
                        v___x_6375_ = v___x_6372_;
                        v_isShared_6376_ = v_isSharedCheck_6405_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_6373_);
                        lean_dec(v___x_6372_);
                        v___x_6375_ = lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6405_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6363_ = lean_box(0);
                v___x_6364_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6364_, 0, v___x_6363_);
                return v___x_6364_;
            }
            2 => {
                if lean_obj_tag(v_val_6373_) == 1 {
                    v_v_6377_ = lean_ctor_get_uint8(v_val_6373_, 0 as u32);
                    lean_dec_ref_known(v_val_6373_, 0);
                    if v_v_6377_ == 0 {
                        lean_del_object(v___x_6375_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6378_ = lean_st_ref_get(v___y_6359_);
                        v_messages_6379_ = lean_ctor_get(v___x_6378_, 1);
                        lean_inc_ref(v_messages_6379_);
                        lean_dec(v___x_6378_);
                        v___x_6380_ = l_Lean_MessageLog_hasErrors(v_messages_6379_);
                        lean_dec_ref(v_messages_6379_);
                        if v___x_6380_ == 0 {
                            v___x_6381_ = lean_st_ref_get(v___y_6359_);
                            v_infoState_6387_ = lean_ctor_get(v___x_6381_, 8);
                            lean_inc_ref(v_infoState_6387_);
                            lean_dec(v___x_6381_);
                            v_enabled_6388_ = lean_ctor_get_uint8(
                                v_infoState_6387_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            lean_dec_ref(v_infoState_6387_);
                            if v_enabled_6388_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_6380_ == 0 {
                                    lean_del_object(v___x_6375_);
                                    v___x_6389_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_List_indexLinter_spec__0___redArg(v___y_6359_);
                                    v_a_6390_ = lean_ctor_get(v___x_6389_, 0);
                                    lean_inc(v_a_6390_);
                                    lean_dec_ref(v___x_6389_);
                                    v___x_6391_ = lean_box(0);
                                    v___x_6392_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_List_listVariablesLinter_spec__6(v_enabled_6388_, v_a_6390_, v___x_6391_, v___y_6358_, v___y_6359_);
                                    lean_dec(v_a_6390_);
                                    if lean_obj_tag(v___x_6392_) == 0 {
                                        v_isSharedCheck_6399_ =
                                            (!lean_is_exclusive(v___x_6392_)) as u8;
                                        if v_isSharedCheck_6399_ == 0 {
                                            v_unused_6400_ = lean_ctor_get(v___x_6392_, 0);
                                            lean_dec(v_unused_6400_);
                                            v___x_6394_ = v___x_6392_;
                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_dec(v___x_6392_);
                                            v___x_6394_ = lean_box(0);
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
                            v___x_6401_ = lean_box(0);
                            if v_isShared_6376_ == 0 {
                                lean_ctor_set_tag(v___x_6375_, 0);
                                lean_ctor_set(v___x_6375_, 0, v___x_6401_);
                                v___x_6403_ = v___x_6375_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_6404_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6404_, 0, v___x_6401_);
                                v___x_6403_ = v_reuseFailAlloc_6404_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_6375_);
                    lean_dec(v_val_6373_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6383_ = lean_box(0);
                if v_isShared_6376_ == 0 {
                    lean_ctor_set_tag(v___x_6375_, 0);
                    lean_ctor_set(v___x_6375_, 0, v___x_6383_);
                    v___x_6385_ = v___x_6375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6386_, 0, v___x_6383_);
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
                    lean_ctor_set(v___x_6394_, 0, v___x_6391_);
                    v___x_6397_ = v___x_6394_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6398_, 0, v___x_6391_);
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
    mut v_stx_6406_: *mut LeanObject,
    mut v___y_6407_: *mut LeanObject,
    mut v___y_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6410_: *mut LeanObject = core::ptr::null_mut();
    v_res_6410_ =
        l_Lean_Linter_List_listVariablesLinter___lam__0(v_stx_6406_, v___y_6407_, v___y_6408_);
    lean_dec(v___y_6408_);
    lean_dec_ref(v___y_6407_);
    lean_dec(v_stx_6406_);
    return v_res_6410_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(
    mut v_as_6424_: *mut LeanObject,
    mut v_as_x27_6425_: *mut LeanObject,
    mut v_b_6426_: *mut LeanObject,
    mut v_a_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_6432_: *mut LeanObject,
    mut v_as_x27_6433_: *mut LeanObject,
    mut v_b_6434_: *mut LeanObject,
    mut v_a_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6439_: *mut LeanObject = core::ptr::null_mut();
    v_res_6439_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__1(
        v_as_6432_,
        v_as_x27_6433_,
        v_b_6434_,
        v_a_6435_,
        v___y_6436_,
        v___y_6437_,
    );
    lean_dec(v___y_6437_);
    lean_dec_ref(v___y_6436_);
    lean_dec(v_as_x27_6433_);
    lean_dec(v_as_6432_);
    return v_res_6439_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(
    mut v_as_6440_: *mut LeanObject,
    mut v_as_x27_6441_: *mut LeanObject,
    mut v_b_6442_: *mut LeanObject,
    mut v_a_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_6448_: *mut LeanObject,
    mut v_as_x27_6449_: *mut LeanObject,
    mut v_b_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
    mut v___y_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6455_: *mut LeanObject = core::ptr::null_mut();
    v_res_6455_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__3(
        v_as_6448_,
        v_as_x27_6449_,
        v_b_6450_,
        v_a_6451_,
        v___y_6452_,
        v___y_6453_,
    );
    lean_dec(v___y_6453_);
    lean_dec_ref(v___y_6452_);
    lean_dec(v_as_x27_6449_);
    lean_dec(v_as_6448_);
    return v_res_6455_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(
    mut v_as_6456_: *mut LeanObject,
    mut v_as_x27_6457_: *mut LeanObject,
    mut v_b_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
    mut v___y_6460_: *mut LeanObject,
    mut v___y_6461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_6464_: *mut LeanObject,
    mut v_as_x27_6465_: *mut LeanObject,
    mut v_b_6466_: *mut LeanObject,
    mut v_a_6467_: *mut LeanObject,
    mut v___y_6468_: *mut LeanObject,
    mut v___y_6469_: *mut LeanObject,
    mut v___y_6470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6471_: *mut LeanObject = core::ptr::null_mut();
    v_res_6471_ = l_List_forIn_x27_loop___at___00Lean_Linter_List_listVariablesLinter_spec__5(
        v_as_6464_,
        v_as_x27_6465_,
        v_b_6466_,
        v_a_6467_,
        v___y_6468_,
        v___y_6469_,
    );
    lean_dec(v___y_6469_);
    lean_dec_ref(v___y_6468_);
    lean_dec(v_as_x27_6465_);
    lean_dec(v_as_6464_);
    return v_res_6471_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    v___x_6473_ = l_Lean_Linter_List_listVariablesLinter;
    v___x_6474_ = l_Lean_Elab_Command_addLinter(v___x_6473_);
    return v___x_6474_;
}
pub unsafe fn l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2____boxed(
    mut v_a_6475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6476_: *mut LeanObject = core::ptr::null_mut();
    v_res_6476_ = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
    return v_res_6476_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_List(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_95049808____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_List_linter_indexVariables = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_List_linter_indexVariables);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_3536400388____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_List_linter_listVariables = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_List_linter_listVariables);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_88313950____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_List_0__Lean_Linter_List_initFn_00___x40_Lean_Linter_List_4228040398____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_List(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_List(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_List(builtin);
}
