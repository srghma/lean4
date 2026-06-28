// Lean compiler output
// Module: Lean.Server.InfoUtils
// Imports: Lean.DocString Lean.PrettyPrinter
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_find_x3f___redArg, l_List_isEmpty___redArg, l_List_mapTR_loop___redArg,
    l_List_max_x3f___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Control::l_List_mapM_loop___redArg;
use crate::r#gen::Init::Data::List::Impl::{
    l___private_Init_Data_List_Impl_0__List_flatMapTR_go, l_List_filterMapTR_go___redArg,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_getTrailingSize, l_Lean_Syntax_structEq};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind, l_Lean_replaceRef, l_id___boxed,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    l_Lean_OptionDecl_fullDescr, l_Lean_Options_empty, l_Lean_getOptionDecls,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_foldlM___redArg, l_Lean_PersistentArray_toList___redArg,
    l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::{
    initialize_Lean_DocString, l_Lean_findDocString_x3f, runtime_initialize_Lean_DocString,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_CompletionInfo_lctx, l_Lean_Elab_CompletionInfo_stx,
    l_Lean_Elab_ContextInfo_runMetaM___redArg, l_Lean_Elab_DelabTermInfo_docString_x3f,
    l_Lean_Elab_Info_toElabInfo_x3f, l_Lean_Elab_Info_updateContext_x3f,
    l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::ErrorExplanation::{
    l_Lean_ErrorExplanation_summaryWithSeverity, l_Lean_errorExplanationExt,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_constName_x3f, l_Lean_Expr_hasMVar, l_Lean_Expr_isSort,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_empty, l_Lean_LocalContext_findFVar_x3f, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_Meta_getPPContext, l_Lean_Meta_ppExpr};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, l_Lean_PrettyPrinter_ppSignature,
    runtime_initialize_Lean_PrettyPrinter,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_Range_contains, l_Lean_Syntax_getRange_x3f};
use crate::r#gen::Lean::Util::Sorry::l_Lean_Expr_isSyntheticSorry;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_utf8_byte_size, lean_usize_dec_eq,
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
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1_value:
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
static mut l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_InfoTree_getCompletionInfos___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_InfoTree_getCompletionInfos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_getCompletionInfos___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_getCompletionInfos___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_InfoTree_getCompletionInfos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_getCompletionInfos___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instBEqHoverableInfoPrio___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instBEqHoverableInfoPrio: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instOrdHoverableInfoPrio___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instOrdHoverableInfoPrio: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instLEHoverableInfoPrio: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instMaxHoverableInfoPrio___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instMaxHoverableInfoPrio: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1_value:
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
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value:
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
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value:
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        101, 118, 97, 108, 87, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97,
        116, 101, 0,
    ],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value
) as *mut LeanObject;
static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_0:
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
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value
        ) as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        12733524109236233889 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value
        ) as *mut LeanObject,
        12377345317205516418 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0_value:
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
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [42, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 96, 96, 108, 101, 97, 110, 10, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [10, 96, 96, 96, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value: LeanStringObject<6> =
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
        m_data: [10, 42, 42, 42, 10, 0],
    };
static mut l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Info_fmtHover_x3f___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Info_fmtHover_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Info_fmtHover_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value) as *mut LeanObject;
static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value: LeanStringObject<4> =
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
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            12966880221525079621 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0(
    mut v_toPure_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    v___x_3593_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3593_, 0, v_a_3592_);
    v___x_3594_ = lean_apply_2(v_toPure_3591_, lean_box(0), v___x_3593_);
    return v___x_3594_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2(
    mut v_postNode_3595_: *mut LeanObject,
    mut v_val_3596_: *mut LeanObject,
    mut v_i_3597_: *mut LeanObject,
    mut v_children_3598_: *mut LeanObject,
    mut v_toBind_3599_: *mut LeanObject,
    mut v___f_3600_: *mut LeanObject,
    mut v_as_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = lean_apply_4(
        v_postNode_3595_,
        v_val_3596_,
        v_i_3597_,
        v_children_3598_,
        v_as_3601_,
    );
    v___x_3603_ = lean_apply_4(
        v_toBind_3599_,
        lean_box(0),
        lean_box(0),
        v___x_3602_,
        v___f_3600_,
    );
    return v___x_3603_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    v___x_3607_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2;
    v___x_3608_ = lean_unsigned_to_nat(21);
    v___x_3609_ = lean_unsigned_to_nat(65);
    v___x_3610_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1;
    v___x_3611_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0;
    v___x_3612_ = l_mkPanicMessageWithDecl(
        v___x_3611_,
        v___x_3610_,
        v___x_3609_,
        v___x_3608_,
        v___x_3607_,
    );
    return v___x_3612_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(
    mut v_postNode_3613_: *mut LeanObject,
    mut v_val_3614_: *mut LeanObject,
    mut v_i_3615_: *mut LeanObject,
    mut v_children_3616_: *mut LeanObject,
    mut v_toBind_3617_: *mut LeanObject,
    mut v___f_3618_: *mut LeanObject,
    mut v_x_3619_: *mut LeanObject,
    mut v_inst_3620_: *mut LeanObject,
    mut v_preNode_3621_: *mut LeanObject,
    mut v___f_3622_: *mut LeanObject,
    mut v_visitChildren_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_visitChildren_boxed_3624_: u8 = 0;
    let mut v_res_3625_: *mut LeanObject = core::ptr::null_mut();
    v_visitChildren_boxed_3624_ = (lean_unbox(v_visitChildren_3623_) as u8);
    v_res_3625_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(
            v_postNode_3613_,
            v_val_3614_,
            v_i_3615_,
            v_children_3616_,
            v_toBind_3617_,
            v___f_3618_,
            v_x_3619_,
            v_inst_3620_,
            v_preNode_3621_,
            v___f_3622_,
            v_visitChildren_boxed_3624_,
        );
    return v_res_3625_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
    mut v_inst_3626_: *mut LeanObject,
    mut v_preNode_3627_: *mut LeanObject,
    mut v_postNode_3628_: *mut LeanObject,
    mut v_x_3629_: *mut LeanObject,
    mut v_x_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3630_) {
                0 => {
                    v_i_3631_ = lean_ctor_get(v_x_3630_, 0);
                    lean_inc_ref(v_i_3631_);
                    v_t_3632_ = lean_ctor_get(v_x_3630_, 1);
                    lean_inc_ref(v_t_3632_);
                    lean_dec_ref_known(v_x_3630_, 2);
                    v___x_3633_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3631_, v_x_3629_);
                    v_x_3629_ = v___x_3633_;
                    v_x_3630_ = v_t_3632_;
                    state = 0;
                    continue;
                }
                1 => {
                    if lean_obj_tag(v_x_3629_) == 0 {
                        lean_dec_ref_known(v_x_3630_, 2);
                        lean_dec(v_postNode_3628_);
                        lean_dec(v_preNode_3627_);
                        v___x_3635_ = lean_box(0);
                        v___x_3636_ = l_instInhabitedOfMonad___redArg(v_inst_3626_, v___x_3635_);
                        v___x_3637_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
                        v___x_3638_ = l_panic___redArg(v___x_3636_, v___x_3637_);
                        lean_dec(v___x_3636_);
                        return v___x_3638_;
                    } else {
                        v_toApplicative_3639_ = lean_ctor_get(v_inst_3626_, 0);
                        v_toBind_3640_ = lean_ctor_get(v_inst_3626_, 1);
                        lean_inc_n(v_toBind_3640_, 3);
                        v_toPure_3641_ = lean_ctor_get(v_toApplicative_3639_, 1);
                        v_i_3642_ = lean_ctor_get(v_x_3630_, 0);
                        lean_inc_ref_n(v_i_3642_, 3);
                        v_children_3643_ = lean_ctor_get(v_x_3630_, 1);
                        lean_inc_ref_n(v_children_3643_, 3);
                        lean_dec_ref_known(v_x_3630_, 2);
                        v_val_3644_ = lean_ctor_get(v_x_3629_, 0);
                        lean_inc_n(v_val_3644_, 3);
                        lean_inc(v_toPure_3641_);
                        v___f_3645_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_3645_, 0, v_toPure_3641_);
                        lean_inc_ref(v___f_3645_);
                        lean_inc(v_postNode_3628_);
                        v___f_3646_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2 as *mut core::ffi::c_void, 7, 6);
                        lean_closure_set(v___f_3646_, 0, v_postNode_3628_);
                        lean_closure_set(v___f_3646_, 1, v_val_3644_);
                        lean_closure_set(v___f_3646_, 2, v_i_3642_);
                        lean_closure_set(v___f_3646_, 3, v_children_3643_);
                        lean_closure_set(v___f_3646_, 4, v_toBind_3640_);
                        lean_closure_set(v___f_3646_, 5, v___f_3645_);
                        lean_inc(v_preNode_3627_);
                        v___f_3647_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 11, 10);
                        lean_closure_set(v___f_3647_, 0, v_postNode_3628_);
                        lean_closure_set(v___f_3647_, 1, v_val_3644_);
                        lean_closure_set(v___f_3647_, 2, v_i_3642_);
                        lean_closure_set(v___f_3647_, 3, v_children_3643_);
                        lean_closure_set(v___f_3647_, 4, v_toBind_3640_);
                        lean_closure_set(v___f_3647_, 5, v___f_3645_);
                        lean_closure_set(v___f_3647_, 6, v_x_3629_);
                        lean_closure_set(v___f_3647_, 7, v_inst_3626_);
                        lean_closure_set(v___f_3647_, 8, v_preNode_3627_);
                        lean_closure_set(v___f_3647_, 9, v___f_3646_);
                        v___x_3648_ =
                            lean_apply_3(v_preNode_3627_, v_val_3644_, v_i_3642_, v_children_3643_);
                        v___x_3649_ = lean_apply_4(
                            v_toBind_3640_,
                            lean_box(0),
                            lean_box(0),
                            v___x_3648_,
                            v___f_3647_,
                        );
                        return v___x_3649_;
                    }
                }
                _ => {
                    v_toApplicative_3650_ = lean_ctor_get(v_inst_3626_, 0);
                    lean_inc_ref(v_toApplicative_3650_);
                    lean_dec_ref_known(v_x_3630_, 1);
                    lean_dec(v_x_3629_);
                    lean_dec(v_postNode_3628_);
                    lean_dec(v_preNode_3627_);
                    lean_dec_ref(v_inst_3626_);
                    v_toPure_3651_ = lean_ctor_get(v_toApplicative_3650_, 1);
                    lean_inc(v_toPure_3651_);
                    lean_dec_ref(v_toApplicative_3650_);
                    v___x_3652_ = lean_box(0);
                    v___x_3653_ = lean_apply_2(v_toPure_3651_, lean_box(0), v___x_3652_);
                    return v___x_3653_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(
    mut v_postNode_3654_: *mut LeanObject,
    mut v_val_3655_: *mut LeanObject,
    mut v_i_3656_: *mut LeanObject,
    mut v_children_3657_: *mut LeanObject,
    mut v_toBind_3658_: *mut LeanObject,
    mut v___f_3659_: *mut LeanObject,
    mut v_x_3660_: *mut LeanObject,
    mut v_inst_3661_: *mut LeanObject,
    mut v_preNode_3662_: *mut LeanObject,
    mut v___f_3663_: *mut LeanObject,
    mut v_visitChildren_3664_: u8,
) -> *mut LeanObject {
    if v_visitChildren_3664_ == 0 {
        let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3663_);
        lean_dec(v_preNode_3662_);
        lean_dec_ref(v_inst_3661_);
        lean_dec(v_x_3660_);
        v___x_3665_ = lean_box(0);
        v___x_3666_ = lean_apply_4(
            v_postNode_3654_,
            v_val_3655_,
            v_i_3656_,
            v_children_3657_,
            v___x_3665_,
        );
        v___x_3667_ = lean_apply_4(
            v_toBind_3658_,
            lean_box(0),
            lean_box(0),
            v___x_3666_,
            v___f_3659_,
        );
        return v___x_3667_;
    } else {
        let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3659_);
        lean_dec_ref(v_val_3655_);
        v___x_3668_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3660_, v_i_3656_);
        lean_dec_ref(v_i_3656_);
        lean_inc_ref(v_inst_3661_);
        v___x_3669_ = lean_alloc_closure(
            l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___x_3669_, 0, v_inst_3661_);
        lean_closure_set(v___x_3669_, 1, v_preNode_3662_);
        lean_closure_set(v___x_3669_, 2, v_postNode_3654_);
        lean_closure_set(v___x_3669_, 3, v___x_3668_);
        v___x_3670_ = l_Lean_PersistentArray_toList___redArg(v_children_3657_);
        lean_dec_ref(v_children_3657_);
        v___x_3671_ = lean_box(0);
        v___x_3672_ =
            l_List_mapM_loop___redArg(v_inst_3661_, v___x_3669_, v___x_3670_, v___x_3671_);
        v___x_3673_ = lean_apply_4(
            v_toBind_3658_,
            lean_box(0),
            lean_box(0),
            v___x_3672_,
            v___f_3663_,
        );
        return v___x_3673_;
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(
    mut v_m_3674_: *mut LeanObject,
    mut v_00_u03b1_3675_: *mut LeanObject,
    mut v_inst_3676_: *mut LeanObject,
    mut v_preNode_3677_: *mut LeanObject,
    mut v_postNode_3678_: *mut LeanObject,
    mut v_x_3679_: *mut LeanObject,
    mut v_x_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_3676_,
        v_preNode_3677_,
        v_postNode_3678_,
        v_x_3679_,
        v_x_3680_,
    );
    return v___x_3681_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM___redArg(
    mut v_inst_3682_: *mut LeanObject,
    mut v_preNode_3683_: *mut LeanObject,
    mut v_postNode_3684_: *mut LeanObject,
    mut v_ctx_x3f_3685_: *mut LeanObject,
    mut v_x_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_3682_,
        v_preNode_3683_,
        v_postNode_3684_,
        v_ctx_x3f_3685_,
        v_x_3686_,
    );
    return v___x_3687_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM(
    mut v_m_3688_: *mut LeanObject,
    mut v_00_u03b1_3689_: *mut LeanObject,
    mut v_inst_3690_: *mut LeanObject,
    mut v_preNode_3691_: *mut LeanObject,
    mut v_postNode_3692_: *mut LeanObject,
    mut v_ctx_x3f_3693_: *mut LeanObject,
    mut v_x_3694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_3690_,
        v_preNode_3691_,
        v_postNode_3692_,
        v_ctx_x3f_3693_,
        v_x_3694_,
    );
    return v___x_3695_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(
    mut v_postNode_3696_: *mut LeanObject,
    mut v_ci_3697_: *mut LeanObject,
    mut v_i_3698_: *mut LeanObject,
    mut v_cs_3699_: *mut LeanObject,
    mut v_x_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3701_ = lean_apply_3(v_postNode_3696_, v_ci_3697_, v_i_3698_, v_cs_3699_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed(
    mut v_postNode_3702_: *mut LeanObject,
    mut v_ci_3703_: *mut LeanObject,
    mut v_i_3704_: *mut LeanObject,
    mut v_cs_3705_: *mut LeanObject,
    mut v_x_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3707_: *mut LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(
        v_postNode_3702_,
        v_ci_3703_,
        v_i_3704_,
        v_cs_3705_,
        v_x_3706_,
    );
    lean_dec(v_x_3706_);
    return v_res_3707_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27___redArg(
    mut v_inst_3708_: *mut LeanObject,
    mut v_preNode_3709_: *mut LeanObject,
    mut v_postNode_3710_: *mut LeanObject,
    mut v_ctx_x3f_3711_: *mut LeanObject,
    mut v_t_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3713_ = lean_ctor_get(v_inst_3708_, 0);
    v_toFunctor_3714_ = lean_ctor_get(v_toApplicative_3713_, 0);
    v_mapConst_3715_ = lean_ctor_get(v_toFunctor_3714_, 1);
    lean_inc(v_mapConst_3715_);
    v___f_3716_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3716_, 0, v_postNode_3710_);
    v___x_3717_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_3708_,
        v_preNode_3709_,
        v___f_3716_,
        v_ctx_x3f_3711_,
        v_t_3712_,
    );
    v___x_3718_ = lean_box(0);
    v___x_3719_ = lean_apply_4(
        v_mapConst_3715_,
        lean_box(0),
        lean_box(0),
        v___x_3718_,
        v___x_3717_,
    );
    return v___x_3719_;
}
pub unsafe fn l_Lean_Elab_InfoTree_visitM_x27(
    mut v_m_3720_: *mut LeanObject,
    mut v_inst_3721_: *mut LeanObject,
    mut v_preNode_3722_: *mut LeanObject,
    mut v_postNode_3723_: *mut LeanObject,
    mut v_ctx_x3f_3724_: *mut LeanObject,
    mut v_t_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    v___x_3726_ = l_Lean_Elab_InfoTree_visitM_x27___redArg(
        v_inst_3721_,
        v_preNode_3722_,
        v_postNode_3723_,
        v_ctx_x3f_3724_,
        v_t_3725_,
    );
    return v___x_3726_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(
    mut v_x_3727_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3727_) == 0 {
        let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
        v___x_3728_ = lean_box(0);
        return v___x_3728_;
    } else {
        let mut v_val_3729_: *mut LeanObject = core::ptr::null_mut();
        v_val_3729_ = lean_ctor_get(v_x_3727_, 0);
        lean_inc(v_val_3729_);
        return v_val_3729_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed(
    mut v_x_3730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3731_: *mut LeanObject = core::ptr::null_mut();
    v_res_3731_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(v_x_3730_);
    lean_dec(v_x_3730_);
    return v_res_3731_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1(
    mut v_p_3735_: *mut LeanObject,
    mut v_ci_3736_: *mut LeanObject,
    mut v_i_3737_: *mut LeanObject,
    mut v_cs_3738_: *mut LeanObject,
    mut v_as_3739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___x_3740_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0;
    v___x_3741_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1;
    v___x_3742_ = l_List_filterMapTR_go___redArg(v___x_3740_, v_as_3739_, v___x_3741_);
    v___x_3743_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(
        lean_box(0),
        lean_box(0),
        v___x_3740_,
        v___x_3742_,
        v___x_3741_,
    );
    v___x_3744_ = lean_apply_4(v_p_3735_, v_ci_3736_, v_i_3737_, v_cs_3738_, v___x_3743_);
    return v___x_3744_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(
    mut v_toPure_3745_: *mut LeanObject,
    mut v_x_3746_: *mut LeanObject,
    mut v_x_3747_: *mut LeanObject,
    mut v_x_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = 1;
    v___x_3750_ = lean_box((v___x_3749_) as usize);
    v___x_3751_ = lean_apply_2(v_toPure_3745_, lean_box(0), v___x_3750_);
    return v___x_3751_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed(
    mut v_toPure_3752_: *mut LeanObject,
    mut v_x_3753_: *mut LeanObject,
    mut v_x_3754_: *mut LeanObject,
    mut v_x_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3756_: *mut LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(
        v_toPure_3752_,
        v_x_3753_,
        v_x_3754_,
        v_x_3755_,
    );
    lean_dec_ref(v_x_3755_);
    lean_dec_ref(v_x_3754_);
    lean_dec_ref(v_x_3753_);
    return v_res_3756_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(
    mut v_inst_3758_: *mut LeanObject,
    mut v_p_3759_: *mut LeanObject,
    mut v_i_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3761_ = lean_ctor_get(v_inst_3758_, 0);
    v_toFunctor_3762_ = lean_ctor_get(v_toApplicative_3761_, 0);
    v_toPure_3763_ = lean_ctor_get(v_toApplicative_3761_, 1);
    v_map_3764_ = lean_ctor_get(v_toFunctor_3762_, 0);
    lean_inc(v_map_3764_);
    v___f_3765_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0;
    v___f_3766_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3766_, 0, v_p_3759_);
    lean_inc(v_toPure_3763_);
    v___f_3767_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3767_, 0, v_toPure_3763_);
    v___x_3768_ = lean_box(0);
    v___x_3769_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_3758_,
        v___f_3767_,
        v___f_3766_,
        v___x_3768_,
        v_i_3760_,
    );
    v___x_3770_ = lean_apply_4(
        v_map_3764_,
        lean_box(0),
        lean_box(0),
        v___f_3765_,
        v___x_3769_,
    );
    return v___x_3770_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM(
    mut v_m_3771_: *mut LeanObject,
    mut v_00_u03b1_3772_: *mut LeanObject,
    mut v_inst_3773_: *mut LeanObject,
    mut v_p_3774_: *mut LeanObject,
    mut v_i_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ =
        l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_3773_, v_p_3774_, v_i_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0(
    mut v_p_3777_: *mut LeanObject,
    mut v_x1_3778_: *mut LeanObject,
    mut v_x2_3779_: *mut LeanObject,
    mut v_x3_3780_: *mut LeanObject,
    mut v_x4_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = lean_apply_4(v_p_3777_, v_x1_3778_, v_x2_3779_, v_x3_3780_, v_x4_3781_);
    return v___x_3782_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3783_) == 0 {
                    v___x_3785_ = lean_array_to_list(v_a_3784_);
                    return v___x_3785_;
                } else {
                    v_head_3786_ = lean_ctor_get(v_a_3783_, 0);
                    lean_inc(v_head_3786_);
                    v_tail_3787_ = lean_ctor_get(v_a_3783_, 1);
                    lean_inc(v_tail_3787_);
                    lean_dec_ref_known(v_a_3783_, 2);
                    v___x_3788_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3784_,
                        v_head_3786_,
                    );
                    v_a_3783_ = v_tail_3787_;
                    v_a_3784_ = v___x_3788_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3790_) == 0 {
                    v___x_3792_ = lean_array_to_list(v_a_3791_);
                    return v___x_3792_;
                } else {
                    v_head_3793_ = lean_ctor_get(v_a_3790_, 0);
                    if lean_obj_tag(v_head_3793_) == 0 {
                        v_tail_3794_ = lean_ctor_get(v_a_3790_, 1);
                        lean_inc(v_tail_3794_);
                        lean_dec_ref_known(v_a_3790_, 2);
                        v_a_3790_ = v_tail_3794_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc_ref(v_head_3793_);
                        v_tail_3796_ = lean_ctor_get(v_a_3790_, 1);
                        lean_inc(v_tail_3796_);
                        lean_dec_ref_known(v_a_3790_, 2);
                        v_val_3797_ = lean_ctor_get(v_head_3793_, 0);
                        lean_inc(v_val_3797_);
                        lean_dec_ref_known(v_head_3793_, 1);
                        v___x_3798_ = lean_array_push(v_a_3791_, v_val_3797_);
                        v_a_3790_ = v_tail_3796_;
                        v_a_3791_ = v___x_3798_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0(
    mut v_p_3800_: *mut LeanObject,
    mut v_ci_3801_: *mut LeanObject,
    mut v_i_3802_: *mut LeanObject,
    mut v_cs_3803_: *mut LeanObject,
    mut v_as_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1;
    v___x_3806_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_as_3804_, v___x_3805_);
    v___x_3807_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v___x_3806_, v___x_3805_);
    v___x_3808_ = lean_apply_4(v_p_3800_, v_ci_3801_, v_i_3802_, v_cs_3803_, v___x_3807_);
    return v___x_3808_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(
    mut v_msg_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___f_3817_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0;
    v___f_3818_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1;
    v___f_3819_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2;
    v___f_3820_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3;
    v___f_3821_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4;
    v___f_3822_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5;
    v___f_3823_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6;
    v___x_3824_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3824_, 0, v___f_3817_);
    lean_ctor_set(v___x_3824_, 1, v___f_3818_);
    v___x_3825_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3825_, 0, v___x_3824_);
    lean_ctor_set(v___x_3825_, 1, v___f_3819_);
    lean_ctor_set(v___x_3825_, 2, v___f_3820_);
    lean_ctor_set(v___x_3825_, 3, v___f_3821_);
    lean_ctor_set(v___x_3825_, 4, v___f_3822_);
    v___x_3826_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    lean_ctor_set(v___x_3826_, 1, v___f_3823_);
    v___x_3827_ = lean_box(0);
    v___x_3828_ = l_instInhabitedOfMonad___redArg(v___x_3826_, v___x_3827_);
    v___x_3829_ = lean_panic_fn_borrowed(v___x_3828_, v_msg_3816_);
    lean_dec(v___x_3828_);
    return v___x_3829_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(
    mut v_preNode_3830_: *mut LeanObject,
    mut v_postNode_3831_: *mut LeanObject,
    mut v_x_3832_: *mut LeanObject,
    mut v_x_3833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_unused_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3833_) {
                0 => {
                    v_i_3834_ = lean_ctor_get(v_x_3833_, 0);
                    lean_inc_ref(v_i_3834_);
                    v_t_3835_ = lean_ctor_get(v_x_3833_, 1);
                    lean_inc_ref(v_t_3835_);
                    lean_dec_ref_known(v_x_3833_, 2);
                    v___x_3836_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3834_, v_x_3832_);
                    v_x_3832_ = v___x_3836_;
                    v_x_3833_ = v_t_3835_;
                    state = 0;
                    continue;
                }
                1 => {
                    if lean_obj_tag(v_x_3832_) == 0 {
                        lean_dec_ref_known(v_x_3833_, 2);
                        lean_dec(v_postNode_3831_);
                        lean_dec_ref(v_preNode_3830_);
                        v___x_3838_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
                        v___x_3839_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v___x_3838_);
                        return v___x_3839_;
                    } else {
                        v_i_3840_ = lean_ctor_get(v_x_3833_, 0);
                        lean_inc_ref_n(v_i_3840_, 2);
                        v_children_3841_ = lean_ctor_get(v_x_3833_, 1);
                        lean_inc_ref_n(v_children_3841_, 2);
                        lean_dec_ref_known(v_x_3833_, 2);
                        v_val_3842_ = lean_ctor_get(v_x_3832_, 0);
                        lean_inc_n(v_val_3842_, 2);
                        lean_inc_ref(v_preNode_3830_);
                        v___x_3843_ =
                            lean_apply_3(v_preNode_3830_, v_val_3842_, v_i_3840_, v_children_3841_);
                        v___x_3844_ = (lean_unbox(v___x_3843_) as u8);
                        if v___x_3844_ == 0 {
                            lean_dec_ref(v_preNode_3830_);
                            v_isSharedCheck_3853_ = (!lean_is_exclusive(v_x_3832_)) as u8;
                            if v_isSharedCheck_3853_ == 0 {
                                v_unused_3854_ = lean_ctor_get(v_x_3832_, 0);
                                lean_dec(v_unused_3854_);
                                v___x_3846_ = v_x_3832_;
                                v_isShared_3847_ = v_isSharedCheck_3853_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_x_3832_);
                                v___x_3846_ = lean_box(0);
                                v_isShared_3847_ = v_isSharedCheck_3853_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3855_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3832_, v_i_3840_);
                            v___x_3856_ = l_Lean_PersistentArray_toList___redArg(v_children_3841_);
                            v___x_3857_ = lean_box(0);
                            lean_inc(v_postNode_3831_);
                            v___x_3858_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_3830_, v_postNode_3831_, v___x_3855_, v___x_3856_, v___x_3857_);
                            v___x_3859_ = lean_apply_4(
                                v_postNode_3831_,
                                v_val_3842_,
                                v_i_3840_,
                                v_children_3841_,
                                v___x_3858_,
                            );
                            v___x_3860_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3860_, 0, v___x_3859_);
                            return v___x_3860_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref_known(v_x_3833_, 1);
                    lean_dec(v_x_3832_);
                    lean_dec(v_postNode_3831_);
                    lean_dec_ref(v_preNode_3830_);
                    v___x_3861_ = lean_box(0);
                    return v___x_3861_;
                }
            },
            1 => {
                v___x_3848_ = lean_box(0);
                v___x_3849_ = lean_apply_4(
                    v_postNode_3831_,
                    v_val_3842_,
                    v_i_3840_,
                    v_children_3841_,
                    v___x_3848_,
                );
                if v_isShared_3847_ == 0 {
                    lean_ctor_set(v___x_3846_, 0, v___x_3849_);
                    v___x_3851_ = v___x_3846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
                    v___x_3851_ = v_reuseFailAlloc_3852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(
    mut v_preNode_3862_: *mut LeanObject,
    mut v_postNode_3863_: *mut LeanObject,
    mut v___x_3864_: *mut LeanObject,
    mut v_x_3865_: *mut LeanObject,
    mut v_x_3866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3865_) == 0 {
                    lean_dec(v___x_3864_);
                    lean_dec(v_postNode_3863_);
                    lean_dec_ref(v_preNode_3862_);
                    v___x_3867_ = l_List_reverse___redArg(v_x_3866_);
                    return v___x_3867_;
                } else {
                    v_head_3868_ = lean_ctor_get(v_x_3865_, 0);
                    v_tail_3869_ = lean_ctor_get(v_x_3865_, 1);
                    v_isSharedCheck_3878_ = (!lean_is_exclusive(v_x_3865_)) as u8;
                    if v_isSharedCheck_3878_ == 0 {
                        v___x_3871_ = v_x_3865_;
                        v_isShared_3872_ = v_isSharedCheck_3878_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3869_);
                        lean_inc(v_head_3868_);
                        lean_dec(v_x_3865_);
                        v___x_3871_ = lean_box(0);
                        v_isShared_3872_ = v_isSharedCheck_3878_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_3864_);
                lean_inc(v_postNode_3863_);
                lean_inc_ref(v_preNode_3862_);
                v___x_3873_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_3862_, v_postNode_3863_, v___x_3864_, v_head_3868_);
                if v_isShared_3872_ == 0 {
                    lean_ctor_set(v___x_3871_, 1, v_x_3866_);
                    lean_ctor_set(v___x_3871_, 0, v___x_3873_);
                    v___x_3875_ = v___x_3871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3873_);
                    lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_x_3866_);
                    v___x_3875_ = v_reuseFailAlloc_3877_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_3865_ = v_tail_3869_;
                v_x_3866_ = v___x_3875_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(
    mut v_x_3879_: *mut LeanObject,
    mut v_x_3880_: *mut LeanObject,
    mut v_x_3881_: *mut LeanObject,
) -> u8 {
    let mut v___x_3882_: u8 = 0;
    v___x_3882_ = 1;
    return v___x_3882_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed(
    mut v_x_3883_: *mut LeanObject,
    mut v_x_3884_: *mut LeanObject,
    mut v_x_3885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3886_: u8 = 0;
    let mut v_r_3887_: *mut LeanObject = core::ptr::null_mut();
    v_res_3886_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(v_x_3883_, v_x_3884_, v_x_3885_);
    lean_dec_ref(v_x_3885_);
    lean_dec_ref(v_x_3884_);
    lean_dec_ref(v_x_3883_);
    v_r_3887_ = lean_box((v_res_3886_) as usize);
    return v_r_3887_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(
    mut v_p_3889_: *mut LeanObject,
    mut v_i_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    v___f_3891_ = lean_alloc_closure(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 5, 1);
    lean_closure_set(v___f_3891_, 0, v_p_3889_);
    v___f_3892_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0;
    v___x_3893_ = lean_box(0);
    v___x_3894_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3892_, v___f_3891_, v___x_3893_, v_i_3890_);
    if lean_obj_tag(v___x_3894_) == 0 {
        let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
        v___x_3895_ = lean_box(0);
        return v___x_3895_;
    } else {
        let mut v_val_3896_: *mut LeanObject = core::ptr::null_mut();
        v_val_3896_ = lean_ctor_get(v___x_3894_, 0);
        lean_inc(v_val_3896_);
        lean_dec_ref_known(v___x_3894_, 1);
        return v_val_3896_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(
    mut v_p_3897_: *mut LeanObject,
    mut v_i_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___f_3899_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3899_, 0, v_p_3897_);
    v___x_3900_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_3899_, v_i_3898_);
    return v___x_3900_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUp(
    mut v_00_u03b1_3901_: *mut LeanObject,
    mut v_p_3902_: *mut LeanObject,
    mut v_i_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    v___x_3904_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v_p_3902_, v_i_3903_);
    return v___x_3904_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0(
    mut v_00_u03b1_3905_: *mut LeanObject,
    mut v_p_3906_: *mut LeanObject,
    mut v_i_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    v___x_3908_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v_p_3906_, v_i_3907_);
    return v___x_3908_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0(
    mut v_00_u03b1_3909_: *mut LeanObject,
    mut v_a_3910_: *mut LeanObject,
    mut v_a_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    v___x_3912_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_a_3910_, v_a_3911_);
    return v___x_3912_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1(
    mut v_00_u03b1_3913_: *mut LeanObject,
    mut v_a_3914_: *mut LeanObject,
    mut v_a_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    v___x_3916_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v_a_3914_, v_a_3915_);
    return v___x_3916_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(
    mut v_00_u03b1_3917_: *mut LeanObject,
    mut v_msg_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    v___x_3919_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v_msg_3918_);
    return v___x_3919_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(
    mut v_00_u03b1_3920_: *mut LeanObject,
    mut v_preNode_3921_: *mut LeanObject,
    mut v_postNode_3922_: *mut LeanObject,
    mut v_x_3923_: *mut LeanObject,
    mut v_x_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    v___x_3925_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_3921_, v_postNode_3922_, v_x_3923_, v_x_3924_);
    return v___x_3925_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(
    mut v_00_u03b1_3926_: *mut LeanObject,
    mut v_preNode_3927_: *mut LeanObject,
    mut v_postNode_3928_: *mut LeanObject,
    mut v___x_3929_: *mut LeanObject,
    mut v_x_3930_: *mut LeanObject,
    mut v_x_3931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_3927_, v_postNode_3928_, v___x_3929_, v_x_3930_, v_x_3931_);
    return v___x_3932_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(
    mut v_inst_3933_: *mut LeanObject,
    mut v_____do__lift_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v_val_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3950_: u8 = 0;
    let mut v_unused_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_3934_) == 0 {
                    v_toApplicative_3935_ = lean_ctor_get(v_inst_3933_, 0);
                    lean_inc_ref(v_toApplicative_3935_);
                    lean_dec_ref(v_inst_3933_);
                    v_toPure_3936_ = lean_ctor_get(v_toApplicative_3935_, 1);
                    lean_inc(v_toPure_3936_);
                    lean_dec_ref(v_toApplicative_3935_);
                    v___x_3937_ = lean_box(0);
                    v___x_3938_ = lean_apply_2(v_toPure_3936_, lean_box(0), v___x_3937_);
                    return v___x_3938_;
                } else {
                    v_toApplicative_3939_ = lean_ctor_get(v_inst_3933_, 0);
                    v_isSharedCheck_3950_ = (!lean_is_exclusive(v_inst_3933_)) as u8;
                    if v_isSharedCheck_3950_ == 0 {
                        v_unused_3951_ = lean_ctor_get(v_inst_3933_, 1);
                        lean_dec(v_unused_3951_);
                        v___x_3941_ = v_inst_3933_;
                        v_isShared_3942_ = v_isSharedCheck_3950_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_toApplicative_3939_);
                        lean_dec(v_inst_3933_);
                        v___x_3941_ = lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_3943_ = lean_ctor_get(v_____do__lift_3934_, 0);
                v_toPure_3944_ = lean_ctor_get(v_toApplicative_3939_, 1);
                lean_inc(v_toPure_3944_);
                lean_dec_ref(v_toApplicative_3939_);
                v___x_3945_ = lean_box(0);
                lean_inc(v_val_3943_);
                if v_isShared_3942_ == 0 {
                    lean_ctor_set_tag(v___x_3941_, 1);
                    lean_ctor_set(v___x_3941_, 1, v___x_3945_);
                    lean_ctor_set(v___x_3941_, 0, v_val_3943_);
                    v___x_3947_ = v___x_3941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_val_3943_);
                    lean_ctor_set(v_reuseFailAlloc_3949_, 1, v___x_3945_);
                    v___x_3947_ = v_reuseFailAlloc_3949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3948_ = lean_apply_2(v_toPure_3944_, lean_box(0), v___x_3947_);
                return v___x_3948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(
    mut v_inst_3952_: *mut LeanObject,
    mut v_____do__lift_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3954_: *mut LeanObject = core::ptr::null_mut();
    v_res_3954_ =
        l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(v_inst_3952_, v_____do__lift_3953_);
    lean_dec(v_____do__lift_3953_);
    return v_res_3954_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(
    mut v_inst_3955_: *mut LeanObject,
    mut v_p_3956_: *mut LeanObject,
    mut v___f_3957_: *mut LeanObject,
    mut v_ctx_3958_: *mut LeanObject,
    mut v_i_3959_: *mut LeanObject,
    mut v_cs_3960_: *mut LeanObject,
    mut v_rs_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: u8 = 0;
    v___x_3962_ = l_List_isEmpty___redArg(v_rs_3961_);
    if v___x_3962_ == 0 {
        let mut v_toApplicative_3963_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_3964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_cs_3960_);
        lean_dec_ref(v_i_3959_);
        lean_dec_ref(v_ctx_3958_);
        lean_dec(v___f_3957_);
        lean_dec(v_p_3956_);
        v_toApplicative_3963_ = lean_ctor_get(v_inst_3955_, 0);
        lean_inc_ref(v_toApplicative_3963_);
        lean_dec_ref(v_inst_3955_);
        v_toPure_3964_ = lean_ctor_get(v_toApplicative_3963_, 1);
        lean_inc(v_toPure_3964_);
        lean_dec_ref(v_toApplicative_3963_);
        v___x_3965_ = lean_apply_2(v_toPure_3964_, lean_box(0), v_rs_3961_);
        return v___x_3965_;
    } else {
        let mut v_toBind_3966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_rs_3961_);
        v_toBind_3966_ = lean_ctor_get(v_inst_3955_, 1);
        lean_inc(v_toBind_3966_);
        lean_dec_ref(v_inst_3955_);
        v___x_3967_ = lean_apply_3(v_p_3956_, v_ctx_3958_, v_i_3959_, v_cs_3960_);
        v___x_3968_ = lean_apply_4(
            v_toBind_3966_,
            lean_box(0),
            lean_box(0),
            v___x_3967_,
            v___f_3957_,
        );
        return v___x_3968_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___redArg(
    mut v_inst_3969_: *mut LeanObject,
    mut v_p_3970_: *mut LeanObject,
    mut v_infoTree_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_3969_, 2);
    v___f_3972_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3972_, 0, v_inst_3969_);
    v___f_3973_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_3973_, 0, v_inst_3969_);
    lean_closure_set(v___f_3973_, 1, v_p_3970_);
    lean_closure_set(v___f_3973_, 2, v___f_3972_);
    v___x_3974_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(
        v_inst_3969_,
        v___f_3973_,
        v_infoTree_3971_,
    );
    return v___x_3974_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM(
    mut v_m_3975_: *mut LeanObject,
    mut v_00_u03b1_3976_: *mut LeanObject,
    mut v_inst_3977_: *mut LeanObject,
    mut v_p_3978_: *mut LeanObject,
    mut v_infoTree_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    v___x_3980_ =
        l_Lean_Elab_InfoTree_deepestNodesM___redArg(v_inst_3977_, v_p_3978_, v_infoTree_3979_);
    return v___x_3980_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(
    mut v_p_3981_: *mut LeanObject,
    mut v_x1_3982_: *mut LeanObject,
    mut v_x2_3983_: *mut LeanObject,
    mut v_x3_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_apply_3(v_p_3981_, v_x1_3982_, v_x2_3983_, v_x3_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(
    mut v_p_3986_: *mut LeanObject,
    mut v_ctx_3987_: *mut LeanObject,
    mut v_i_3988_: *mut LeanObject,
    mut v_cs_3989_: *mut LeanObject,
    mut v_rs_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3991_: u8 = 0;
    v___x_3991_ = l_List_isEmpty___redArg(v_rs_3990_);
    if v___x_3991_ == 0 {
        lean_dec_ref(v_cs_3989_);
        lean_dec_ref(v_i_3988_);
        lean_dec_ref(v_ctx_3987_);
        lean_dec_ref(v_p_3986_);
        lean_inc(v_rs_3990_);
        return v_rs_3990_;
    } else {
        let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
        v___x_3992_ = lean_apply_3(v_p_3986_, v_ctx_3987_, v_i_3988_, v_cs_3989_);
        if lean_obj_tag(v___x_3992_) == 0 {
            let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
            v___x_3993_ = lean_box(0);
            return v___x_3993_;
        } else {
            let mut v_val_3994_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
            v_val_3994_ = lean_ctor_get(v___x_3992_, 0);
            lean_inc(v_val_3994_);
            lean_dec_ref_known(v___x_3992_, 1);
            v___x_3995_ = lean_box(0);
            v___x_3996_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_3996_, 0, v_val_3994_);
            lean_ctor_set(v___x_3996_, 1, v___x_3995_);
            return v___x_3996_;
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(
    mut v_p_3997_: *mut LeanObject,
    mut v_ctx_3998_: *mut LeanObject,
    mut v_i_3999_: *mut LeanObject,
    mut v_cs_4000_: *mut LeanObject,
    mut v_rs_4001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4002_: *mut LeanObject = core::ptr::null_mut();
    v_res_4002_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(v_p_3997_, v_ctx_3998_, v_i_3999_, v_cs_4000_, v_rs_4001_);
    lean_dec(v_rs_4001_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(
    mut v_p_4003_: *mut LeanObject,
    mut v_infoTree_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    v___f_4005_ = lean_alloc_closure(l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
    lean_closure_set(v___f_4005_, 0, v_p_4003_);
    v___x_4006_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_4005_, v_infoTree_4004_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodes___redArg(
    mut v_p_4007_: *mut LeanObject,
    mut v_infoTree_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___f_4009_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4009_, 0, v_p_4007_);
    v___x_4010_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v___f_4009_, v_infoTree_4008_);
    return v___x_4010_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodes(
    mut v_00_u03b1_4011_: *mut LeanObject,
    mut v_p_4012_: *mut LeanObject,
    mut v_infoTree_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v_p_4012_, v_infoTree_4013_);
    return v___x_4014_;
}
pub unsafe fn l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(
    mut v_00_u03b1_4015_: *mut LeanObject,
    mut v_p_4016_: *mut LeanObject,
    mut v_infoTree_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    v___x_4018_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v_p_4016_, v_infoTree_4017_);
    return v___x_4018_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_4019_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(
    mut v_f_4020_: *mut LeanObject,
    mut v___x_4021_: *mut LeanObject,
    mut v_x_4022_: *mut LeanObject,
    mut v_x_4023_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4022_) == 0 {
        let mut v_cs_4024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4027_: u8 = 0;
        v_cs_4024_ = lean_ctor_get(v_x_4022_, 0);
        v___x_4025_ = lean_unsigned_to_nat(0);
        v___x_4026_ = lean_array_get_size(v_cs_4024_);
        v___x_4027_ = lean_nat_dec_lt(v___x_4025_, v___x_4026_);
        if v___x_4027_ == 0 {
            lean_dec(v___x_4021_);
            lean_dec(v_f_4020_);
            return v_x_4023_;
        } else {
            let mut v___x_4028_: u8 = 0;
            v___x_4028_ = lean_nat_dec_le(v___x_4026_, v___x_4026_);
            if v___x_4028_ == 0 {
                if v___x_4027_ == 0 {
                    lean_dec(v___x_4021_);
                    lean_dec(v_f_4020_);
                    return v_x_4023_;
                } else {
                    let mut v___x_4029_: usize = 0;
                    let mut v___x_4030_: usize = 0;
                    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4029_ = 0usize;
                    v___x_4030_ = lean_usize_of_nat(v___x_4026_);
                    v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4020_, v___x_4021_, v_cs_4024_, v___x_4029_, v___x_4030_, v_x_4023_);
                    return v___x_4031_;
                }
            } else {
                let mut v___x_4032_: usize = 0;
                let mut v___x_4033_: usize = 0;
                let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
                v___x_4032_ = 0usize;
                v___x_4033_ = lean_usize_of_nat(v___x_4026_);
                v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4020_, v___x_4021_, v_cs_4024_, v___x_4032_, v___x_4033_, v_x_4023_);
                return v___x_4034_;
            }
        }
    } else {
        let mut v_vs_4035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4038_: u8 = 0;
        v_vs_4035_ = lean_ctor_get(v_x_4022_, 0);
        v___x_4036_ = lean_unsigned_to_nat(0);
        v___x_4037_ = lean_array_get_size(v_vs_4035_);
        v___x_4038_ = lean_nat_dec_lt(v___x_4036_, v___x_4037_);
        if v___x_4038_ == 0 {
            lean_dec(v___x_4021_);
            lean_dec(v_f_4020_);
            return v_x_4023_;
        } else {
            let mut v___x_4039_: u8 = 0;
            v___x_4039_ = lean_nat_dec_le(v___x_4037_, v___x_4037_);
            if v___x_4039_ == 0 {
                if v___x_4038_ == 0 {
                    lean_dec(v___x_4021_);
                    lean_dec(v_f_4020_);
                    return v_x_4023_;
                } else {
                    let mut v___x_4040_: usize = 0;
                    let mut v___x_4041_: usize = 0;
                    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4040_ = 0usize;
                    v___x_4041_ = lean_usize_of_nat(v___x_4037_);
                    v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4020_, v___x_4021_, v_vs_4035_, v___x_4040_, v___x_4041_, v_x_4023_);
                    return v___x_4042_;
                }
            } else {
                let mut v___x_4043_: usize = 0;
                let mut v___x_4044_: usize = 0;
                let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
                v___x_4043_ = 0usize;
                v___x_4044_ = lean_usize_of_nat(v___x_4037_);
                v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4020_, v___x_4021_, v_vs_4035_, v___x_4043_, v___x_4044_, v_x_4023_);
                return v___x_4045_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(
    mut v_f_4046_: *mut LeanObject,
    mut v___x_4047_: *mut LeanObject,
    mut v_as_4048_: *mut LeanObject,
    mut v_i_4049_: usize,
    mut v_stop_4050_: usize,
    mut v_b_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4052_: u8 = 0;
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: usize = 0;
    let mut v___x_4056_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4052_ = lean_usize_dec_eq(v_i_4049_, v_stop_4050_);
                if v___x_4052_ == 0 {
                    v___x_4053_ = lean_array_uget_borrowed(v_as_4048_, v_i_4049_);
                    lean_inc(v___x_4047_);
                    lean_inc(v_f_4046_);
                    v___x_4054_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_4046_, v___x_4047_, v___x_4053_, v_b_4051_);
                    v___x_4055_ = 1usize;
                    v___x_4056_ = lean_usize_add(v_i_4049_, v___x_4055_);
                    v_i_4049_ = v___x_4056_;
                    v_b_4051_ = v___x_4054_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_4047_);
                    lean_dec(v_f_4046_);
                    return v_b_4051_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(
    mut v_f_4058_: *mut LeanObject,
    mut v___x_4059_: *mut LeanObject,
    mut v_x_4060_: *mut LeanObject,
    mut v_x_4061_: usize,
    mut v_x_4062_: usize,
    mut v_x_4063_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4060_) == 0 {
        let mut v_cs_4064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4066_: usize = 0;
        let mut v_j_4067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: usize = 0;
        let mut v___x_4070_: usize = 0;
        let mut v___x_4071_: usize = 0;
        let mut v___x_4072_: usize = 0;
        let mut v___x_4073_: usize = 0;
        let mut v___x_4074_: usize = 0;
        let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4079_: u8 = 0;
        v_cs_4064_ = lean_ctor_get(v_x_4060_, 0);
        v___x_4065_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
        v___x_4066_ = lean_usize_shift_right(v_x_4061_, v_x_4062_);
        v_j_4067_ = lean_usize_to_nat(v___x_4066_);
        v___x_4068_ = lean_array_get_borrowed(v___x_4065_, v_cs_4064_, v_j_4067_);
        v___x_4069_ = 1usize;
        v___x_4070_ = lean_usize_shift_left(v___x_4069_, v_x_4062_);
        v___x_4071_ = lean_usize_sub(v___x_4070_, v___x_4069_);
        v___x_4072_ = lean_usize_land(v_x_4061_, v___x_4071_);
        v___x_4073_ = 5usize;
        v___x_4074_ = lean_usize_sub(v_x_4062_, v___x_4073_);
        lean_inc(v___x_4059_);
        lean_inc(v_f_4058_);
        v___x_4075_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_4058_, v___x_4059_, v___x_4068_, v___x_4072_, v___x_4074_, v_x_4063_);
        v___x_4076_ = lean_unsigned_to_nat(1);
        v___x_4077_ = lean_nat_add(v_j_4067_, v___x_4076_);
        lean_dec(v_j_4067_);
        v___x_4078_ = lean_array_get_size(v_cs_4064_);
        v___x_4079_ = lean_nat_dec_lt(v___x_4077_, v___x_4078_);
        if v___x_4079_ == 0 {
            lean_dec(v___x_4077_);
            lean_dec(v___x_4059_);
            lean_dec(v_f_4058_);
            return v___x_4075_;
        } else {
            let mut v___x_4080_: u8 = 0;
            v___x_4080_ = lean_nat_dec_le(v___x_4078_, v___x_4078_);
            if v___x_4080_ == 0 {
                if v___x_4079_ == 0 {
                    lean_dec(v___x_4077_);
                    lean_dec(v___x_4059_);
                    lean_dec(v_f_4058_);
                    return v___x_4075_;
                } else {
                    let mut v___x_4081_: usize = 0;
                    let mut v___x_4082_: usize = 0;
                    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4081_ = lean_usize_of_nat(v___x_4077_);
                    lean_dec(v___x_4077_);
                    v___x_4082_ = lean_usize_of_nat(v___x_4078_);
                    v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4058_, v___x_4059_, v_cs_4064_, v___x_4081_, v___x_4082_, v___x_4075_);
                    return v___x_4083_;
                }
            } else {
                let mut v___x_4084_: usize = 0;
                let mut v___x_4085_: usize = 0;
                let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
                v___x_4084_ = lean_usize_of_nat(v___x_4077_);
                lean_dec(v___x_4077_);
                v___x_4085_ = lean_usize_of_nat(v___x_4078_);
                v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4058_, v___x_4059_, v_cs_4064_, v___x_4084_, v___x_4085_, v___x_4075_);
                return v___x_4086_;
            }
        }
    } else {
        let mut v_vs_4087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4090_: u8 = 0;
        v_vs_4087_ = lean_ctor_get(v_x_4060_, 0);
        v___x_4088_ = lean_usize_to_nat(v_x_4061_);
        v___x_4089_ = lean_array_get_size(v_vs_4087_);
        v___x_4090_ = lean_nat_dec_lt(v___x_4088_, v___x_4089_);
        if v___x_4090_ == 0 {
            lean_dec(v___x_4088_);
            lean_dec(v___x_4059_);
            lean_dec(v_f_4058_);
            return v_x_4063_;
        } else {
            let mut v___x_4091_: u8 = 0;
            v___x_4091_ = lean_nat_dec_le(v___x_4089_, v___x_4089_);
            if v___x_4091_ == 0 {
                if v___x_4090_ == 0 {
                    lean_dec(v___x_4088_);
                    lean_dec(v___x_4059_);
                    lean_dec(v_f_4058_);
                    return v_x_4063_;
                } else {
                    let mut v___x_4092_: usize = 0;
                    let mut v___x_4093_: usize = 0;
                    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4092_ = lean_usize_of_nat(v___x_4088_);
                    lean_dec(v___x_4088_);
                    v___x_4093_ = lean_usize_of_nat(v___x_4089_);
                    v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4058_, v___x_4059_, v_vs_4087_, v___x_4092_, v___x_4093_, v_x_4063_);
                    return v___x_4094_;
                }
            } else {
                let mut v___x_4095_: usize = 0;
                let mut v___x_4096_: usize = 0;
                let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
                v___x_4095_ = lean_usize_of_nat(v___x_4088_);
                lean_dec(v___x_4088_);
                v___x_4096_ = lean_usize_of_nat(v___x_4089_);
                v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4058_, v___x_4059_, v_vs_4087_, v___x_4095_, v___x_4096_, v_x_4063_);
                return v___x_4097_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(
    mut v_f_4098_: *mut LeanObject,
    mut v___x_4099_: *mut LeanObject,
    mut v_t_4100_: *mut LeanObject,
    mut v_init_4101_: *mut LeanObject,
    mut v_start_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    v___x_4103_ = lean_unsigned_to_nat(0);
    v___x_4104_ = lean_nat_dec_eq(v_start_4102_, v___x_4103_);
    if v___x_4104_ == 0 {
        let mut v_root_4105_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4106_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_4107_: usize = 0;
        let mut v_tailOff_4108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4109_: u8 = 0;
        v_root_4105_ = lean_ctor_get(v_t_4100_, 0);
        v_tail_4106_ = lean_ctor_get(v_t_4100_, 1);
        v_shift_4107_ = lean_ctor_get_usize(v_t_4100_, 4);
        v_tailOff_4108_ = lean_ctor_get(v_t_4100_, 3);
        v___x_4109_ = lean_nat_dec_le(v_tailOff_4108_, v_start_4102_);
        if v___x_4109_ == 0 {
            let mut v___x_4110_: usize = 0;
            let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4113_: u8 = 0;
            v___x_4110_ = lean_usize_of_nat(v_start_4102_);
            lean_inc(v___x_4099_);
            lean_inc(v_f_4098_);
            v___x_4111_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_4098_, v___x_4099_, v_root_4105_, v___x_4110_, v_shift_4107_, v_init_4101_);
            v___x_4112_ = lean_array_get_size(v_tail_4106_);
            v___x_4113_ = lean_nat_dec_lt(v___x_4103_, v___x_4112_);
            if v___x_4113_ == 0 {
                lean_dec(v___x_4099_);
                lean_dec(v_f_4098_);
                return v___x_4111_;
            } else {
                let mut v___x_4114_: u8 = 0;
                v___x_4114_ = lean_nat_dec_le(v___x_4112_, v___x_4112_);
                if v___x_4114_ == 0 {
                    if v___x_4113_ == 0 {
                        lean_dec(v___x_4099_);
                        lean_dec(v_f_4098_);
                        return v___x_4111_;
                    } else {
                        let mut v___x_4115_: usize = 0;
                        let mut v___x_4116_: usize = 0;
                        let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4115_ = 0usize;
                        v___x_4116_ = lean_usize_of_nat(v___x_4112_);
                        v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4106_, v___x_4115_, v___x_4116_, v___x_4111_);
                        return v___x_4117_;
                    }
                } else {
                    let mut v___x_4118_: usize = 0;
                    let mut v___x_4119_: usize = 0;
                    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4118_ = 0usize;
                    v___x_4119_ = lean_usize_of_nat(v___x_4112_);
                    v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4106_, v___x_4118_, v___x_4119_, v___x_4111_);
                    return v___x_4120_;
                }
            }
        } else {
            let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4123_: u8 = 0;
            v___x_4121_ = lean_nat_sub(v_start_4102_, v_tailOff_4108_);
            v___x_4122_ = lean_array_get_size(v_tail_4106_);
            v___x_4123_ = lean_nat_dec_lt(v___x_4121_, v___x_4122_);
            if v___x_4123_ == 0 {
                lean_dec(v___x_4121_);
                lean_dec(v___x_4099_);
                lean_dec(v_f_4098_);
                return v_init_4101_;
            } else {
                let mut v___x_4124_: u8 = 0;
                v___x_4124_ = lean_nat_dec_le(v___x_4122_, v___x_4122_);
                if v___x_4124_ == 0 {
                    if v___x_4123_ == 0 {
                        lean_dec(v___x_4121_);
                        lean_dec(v___x_4099_);
                        lean_dec(v_f_4098_);
                        return v_init_4101_;
                    } else {
                        let mut v___x_4125_: usize = 0;
                        let mut v___x_4126_: usize = 0;
                        let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4125_ = lean_usize_of_nat(v___x_4121_);
                        lean_dec(v___x_4121_);
                        v___x_4126_ = lean_usize_of_nat(v___x_4122_);
                        v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4106_, v___x_4125_, v___x_4126_, v_init_4101_);
                        return v___x_4127_;
                    }
                } else {
                    let mut v___x_4128_: usize = 0;
                    let mut v___x_4129_: usize = 0;
                    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4128_ = lean_usize_of_nat(v___x_4121_);
                    lean_dec(v___x_4121_);
                    v___x_4129_ = lean_usize_of_nat(v___x_4122_);
                    v___x_4130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4106_, v___x_4128_, v___x_4129_, v_init_4101_);
                    return v___x_4130_;
                }
            }
        }
    } else {
        let mut v_root_4131_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4135_: u8 = 0;
        v_root_4131_ = lean_ctor_get(v_t_4100_, 0);
        v_tail_4132_ = lean_ctor_get(v_t_4100_, 1);
        lean_inc(v___x_4099_);
        lean_inc(v_f_4098_);
        v___x_4133_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_4098_, v___x_4099_, v_root_4131_, v_init_4101_);
        v___x_4134_ = lean_array_get_size(v_tail_4132_);
        v___x_4135_ = lean_nat_dec_lt(v___x_4103_, v___x_4134_);
        if v___x_4135_ == 0 {
            lean_dec(v___x_4099_);
            lean_dec(v_f_4098_);
            return v___x_4133_;
        } else {
            let mut v___x_4136_: u8 = 0;
            v___x_4136_ = lean_nat_dec_le(v___x_4134_, v___x_4134_);
            if v___x_4136_ == 0 {
                if v___x_4135_ == 0 {
                    lean_dec(v___x_4099_);
                    lean_dec(v_f_4098_);
                    return v___x_4133_;
                } else {
                    let mut v___x_4137_: usize = 0;
                    let mut v___x_4138_: usize = 0;
                    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4137_ = 0usize;
                    v___x_4138_ = lean_usize_of_nat(v___x_4134_);
                    v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4132_, v___x_4137_, v___x_4138_, v___x_4133_);
                    return v___x_4139_;
                }
            } else {
                let mut v___x_4140_: usize = 0;
                let mut v___x_4141_: usize = 0;
                let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
                v___x_4140_ = 0usize;
                v___x_4141_ = lean_usize_of_nat(v___x_4134_);
                v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4098_, v___x_4099_, v_tail_4132_, v___x_4140_, v___x_4141_, v___x_4133_);
                return v___x_4142_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(
    mut v_f_4143_: *mut LeanObject,
    mut v_ctx_x3f_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
    mut v_x_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4146_) {
                0 => {
                    v_i_4147_ = lean_ctor_get(v_x_4146_, 0);
                    lean_inc_ref(v_i_4147_);
                    v_t_4148_ = lean_ctor_get(v_x_4146_, 1);
                    lean_inc_ref(v_t_4148_);
                    lean_dec_ref_known(v_x_4146_, 2);
                    v___x_4149_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_4147_,
                        v_ctx_x3f_4144_,
                    );
                    v_ctx_x3f_4144_ = v___x_4149_;
                    v_x_4146_ = v_t_4148_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_4151_ = lean_ctor_get(v_x_4146_, 0);
                    lean_inc_ref(v_i_4151_);
                    v_children_4152_ = lean_ctor_get(v_x_4146_, 1);
                    lean_inc_ref(v_children_4152_);
                    lean_dec_ref_known(v_x_4146_, 2);
                    if lean_obj_tag(v_ctx_x3f_4144_) == 0 {
                        v___y_4154_ = v_a_4145_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4158_ = lean_ctor_get(v_ctx_x3f_4144_, 0);
                        lean_inc(v_f_4143_);
                        lean_inc_ref(v_i_4151_);
                        lean_inc(v_val_4158_);
                        v___x_4159_ = lean_apply_3(v_f_4143_, v_val_4158_, v_i_4151_, v_a_4145_);
                        v___y_4154_ = v___x_4159_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref_known(v_x_4146_, 1);
                    lean_dec(v_ctx_x3f_4144_);
                    lean_dec(v_f_4143_);
                    return v_a_4145_;
                }
            },
            1 => {
                v___x_4155_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_4144_, v_i_4151_);
                lean_dec_ref(v_i_4151_);
                v___x_4156_ = lean_unsigned_to_nat(0);
                v___x_4157_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_4143_, v___x_4155_, v_children_4152_, v___y_4154_, v___x_4156_);
                lean_dec_ref(v_children_4152_);
                return v___x_4157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(
    mut v_f_4160_: *mut LeanObject,
    mut v___x_4161_: *mut LeanObject,
    mut v_as_4162_: *mut LeanObject,
    mut v_i_4163_: usize,
    mut v_stop_4164_: usize,
    mut v_b_4165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: usize = 0;
    let mut v___x_4170_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4166_ = lean_usize_dec_eq(v_i_4163_, v_stop_4164_);
                if v___x_4166_ == 0 {
                    v___x_4167_ = lean_array_uget_borrowed(v_as_4162_, v_i_4163_);
                    lean_inc(v___x_4167_);
                    lean_inc(v___x_4161_);
                    lean_inc(v_f_4160_);
                    v___x_4168_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_4160_, v___x_4161_, v_b_4165_, v___x_4167_);
                    v___x_4169_ = 1usize;
                    v___x_4170_ = lean_usize_add(v_i_4163_, v___x_4169_);
                    v_i_4163_ = v___x_4170_;
                    v_b_4165_ = v___x_4168_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_4161_);
                    lean_dec(v_f_4160_);
                    return v_b_4165_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(
    mut v_f_4172_: *mut LeanObject,
    mut v___x_4173_: *mut LeanObject,
    mut v_as_4174_: *mut LeanObject,
    mut v_i_4175_: *mut LeanObject,
    mut v_stop_4176_: *mut LeanObject,
    mut v_b_4177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4178_: usize = 0;
    let mut v_stop_boxed_4179_: usize = 0;
    let mut v_res_4180_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4178_ = lean_unbox_usize(v_i_4175_);
    lean_dec(v_i_4175_);
    v_stop_boxed_4179_ = lean_unbox_usize(v_stop_4176_);
    lean_dec(v_stop_4176_);
    v_res_4180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4172_, v___x_4173_, v_as_4174_, v_i_boxed_4178_, v_stop_boxed_4179_, v_b_4177_);
    lean_dec_ref(v_as_4174_);
    return v_res_4180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_4181_: *mut LeanObject,
    mut v___x_4182_: *mut LeanObject,
    mut v_as_4183_: *mut LeanObject,
    mut v_i_4184_: *mut LeanObject,
    mut v_stop_4185_: *mut LeanObject,
    mut v_b_4186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4187_: usize = 0;
    let mut v_stop_boxed_4188_: usize = 0;
    let mut v_res_4189_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4187_ = lean_unbox_usize(v_i_4184_);
    lean_dec(v_i_4184_);
    v_stop_boxed_4188_ = lean_unbox_usize(v_stop_4185_);
    lean_dec(v_stop_4185_);
    v_res_4189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4181_, v___x_4182_, v_as_4183_, v_i_boxed_4187_, v_stop_boxed_4188_, v_b_4186_);
    lean_dec_ref(v_as_4183_);
    return v_res_4189_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(
    mut v_f_4190_: *mut LeanObject,
    mut v___x_4191_: *mut LeanObject,
    mut v_x_4192_: *mut LeanObject,
    mut v_x_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4194_: *mut LeanObject = core::ptr::null_mut();
    v_res_4194_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_4190_, v___x_4191_, v_x_4192_, v_x_4193_);
    lean_dec_ref(v_x_4192_);
    return v_res_4194_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(
    mut v_f_4195_: *mut LeanObject,
    mut v___x_4196_: *mut LeanObject,
    mut v_x_4197_: *mut LeanObject,
    mut v_x_4198_: *mut LeanObject,
    mut v_x_4199_: *mut LeanObject,
    mut v_x_4200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1543__boxed_4201_: usize = 0;
    let mut v_x_1544__boxed_4202_: usize = 0;
    let mut v_res_4203_: *mut LeanObject = core::ptr::null_mut();
    v_x_1543__boxed_4201_ = lean_unbox_usize(v_x_4198_);
    lean_dec(v_x_4198_);
    v_x_1544__boxed_4202_ = lean_unbox_usize(v_x_4199_);
    lean_dec(v_x_4199_);
    v_res_4203_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_4195_, v___x_4196_, v_x_4197_, v_x_1543__boxed_4201_, v_x_1544__boxed_4202_, v_x_4200_);
    lean_dec_ref(v_x_4197_);
    return v_res_4203_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(
    mut v_f_4204_: *mut LeanObject,
    mut v___x_4205_: *mut LeanObject,
    mut v_t_4206_: *mut LeanObject,
    mut v_init_4207_: *mut LeanObject,
    mut v_start_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4209_: *mut LeanObject = core::ptr::null_mut();
    v_res_4209_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_4204_, v___x_4205_, v_t_4206_, v_init_4207_, v_start_4208_);
    lean_dec(v_start_4208_);
    lean_dec_ref(v_t_4206_);
    return v_res_4209_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go(
    mut v_00_u03b1_4210_: *mut LeanObject,
    mut v_f_4211_: *mut LeanObject,
    mut v_ctx_x3f_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
    mut v_x_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    v___x_4215_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(
        v_f_4211_,
        v_ctx_x3f_4212_,
        v_a_4213_,
        v_x_4214_,
    );
    return v___x_4215_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(
    mut v_00_u03b1_4216_: *mut LeanObject,
    mut v_f_4217_: *mut LeanObject,
    mut v___x_4218_: *mut LeanObject,
    mut v_t_4219_: *mut LeanObject,
    mut v_init_4220_: *mut LeanObject,
    mut v_start_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    v___x_4222_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_4217_, v___x_4218_, v_t_4219_, v_init_4220_, v_start_4221_);
    return v___x_4222_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(
    mut v_00_u03b1_4223_: *mut LeanObject,
    mut v_f_4224_: *mut LeanObject,
    mut v___x_4225_: *mut LeanObject,
    mut v_t_4226_: *mut LeanObject,
    mut v_init_4227_: *mut LeanObject,
    mut v_start_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4229_: *mut LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(v_00_u03b1_4223_, v_f_4224_, v___x_4225_, v_t_4226_, v_init_4227_, v_start_4228_);
    lean_dec(v_start_4228_);
    lean_dec_ref(v_t_4226_);
    return v_res_4229_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(
    mut v_00_u03b1_4230_: *mut LeanObject,
    mut v_f_4231_: *mut LeanObject,
    mut v___x_4232_: *mut LeanObject,
    mut v_x_4233_: *mut LeanObject,
    mut v_x_4234_: usize,
    mut v_x_4235_: usize,
    mut v_x_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    v___x_4237_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_4231_, v___x_4232_, v_x_4233_, v_x_4234_, v_x_4235_, v_x_4236_);
    return v___x_4237_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(
    mut v_00_u03b1_4238_: *mut LeanObject,
    mut v_f_4239_: *mut LeanObject,
    mut v___x_4240_: *mut LeanObject,
    mut v_x_4241_: *mut LeanObject,
    mut v_x_4242_: *mut LeanObject,
    mut v_x_4243_: *mut LeanObject,
    mut v_x_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1763__boxed_4245_: usize = 0;
    let mut v_x_1764__boxed_4246_: usize = 0;
    let mut v_res_4247_: *mut LeanObject = core::ptr::null_mut();
    v_x_1763__boxed_4245_ = lean_unbox_usize(v_x_4242_);
    lean_dec(v_x_4242_);
    v_x_1764__boxed_4246_ = lean_unbox_usize(v_x_4243_);
    lean_dec(v_x_4243_);
    v_res_4247_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(v_00_u03b1_4238_, v_f_4239_, v___x_4240_, v_x_4241_, v_x_1763__boxed_4245_, v_x_1764__boxed_4246_, v_x_4244_);
    lean_dec_ref(v_x_4241_);
    return v_res_4247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(
    mut v_00_u03b1_4248_: *mut LeanObject,
    mut v_f_4249_: *mut LeanObject,
    mut v___x_4250_: *mut LeanObject,
    mut v_as_4251_: *mut LeanObject,
    mut v_i_4252_: usize,
    mut v_stop_4253_: usize,
    mut v_b_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_4249_, v___x_4250_, v_as_4251_, v_i_4252_, v_stop_4253_, v_b_4254_);
    return v___x_4255_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(
    mut v_00_u03b1_4256_: *mut LeanObject,
    mut v_f_4257_: *mut LeanObject,
    mut v___x_4258_: *mut LeanObject,
    mut v_as_4259_: *mut LeanObject,
    mut v_i_4260_: *mut LeanObject,
    mut v_stop_4261_: *mut LeanObject,
    mut v_b_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4263_: usize = 0;
    let mut v_stop_boxed_4264_: usize = 0;
    let mut v_res_4265_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4263_ = lean_unbox_usize(v_i_4260_);
    lean_dec(v_i_4260_);
    v_stop_boxed_4264_ = lean_unbox_usize(v_stop_4261_);
    lean_dec(v_stop_4261_);
    v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(v_00_u03b1_4256_, v_f_4257_, v___x_4258_, v_as_4259_, v_i_boxed_4263_, v_stop_boxed_4264_, v_b_4262_);
    lean_dec_ref(v_as_4259_);
    return v_res_4265_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(
    mut v_00_u03b1_4266_: *mut LeanObject,
    mut v_f_4267_: *mut LeanObject,
    mut v___x_4268_: *mut LeanObject,
    mut v_x_4269_: *mut LeanObject,
    mut v_x_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    v___x_4271_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_4267_, v___x_4268_, v_x_4269_, v_x_4270_);
    return v___x_4271_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(
    mut v_00_u03b1_4272_: *mut LeanObject,
    mut v_f_4273_: *mut LeanObject,
    mut v___x_4274_: *mut LeanObject,
    mut v_x_4275_: *mut LeanObject,
    mut v_x_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4277_: *mut LeanObject = core::ptr::null_mut();
    v_res_4277_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(v_00_u03b1_4272_, v_f_4273_, v___x_4274_, v_x_4275_, v_x_4276_);
    lean_dec_ref(v_x_4275_);
    return v_res_4277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4278_: *mut LeanObject,
    mut v_f_4279_: *mut LeanObject,
    mut v___x_4280_: *mut LeanObject,
    mut v_as_4281_: *mut LeanObject,
    mut v_i_4282_: usize,
    mut v_stop_4283_: usize,
    mut v_b_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_4279_, v___x_4280_, v_as_4281_, v_i_4282_, v_stop_4283_, v_b_4284_);
    return v___x_4285_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4286_: *mut LeanObject,
    mut v_f_4287_: *mut LeanObject,
    mut v___x_4288_: *mut LeanObject,
    mut v_as_4289_: *mut LeanObject,
    mut v_i_4290_: *mut LeanObject,
    mut v_stop_4291_: *mut LeanObject,
    mut v_b_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4293_: usize = 0;
    let mut v_stop_boxed_4294_: usize = 0;
    let mut v_res_4295_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4293_ = lean_unbox_usize(v_i_4290_);
    lean_dec(v_i_4290_);
    v_stop_boxed_4294_ = lean_unbox_usize(v_stop_4291_);
    lean_dec(v_stop_4291_);
    v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(v_00_u03b1_4286_, v_f_4287_, v___x_4288_, v_as_4289_, v_i_boxed_4293_, v_stop_boxed_4294_, v_b_4292_);
    lean_dec_ref(v_as_4289_);
    return v_res_4295_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfo___redArg(
    mut v_f_4296_: *mut LeanObject,
    mut v_init_4297_: *mut LeanObject,
    mut v_x_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    v___x_4299_ = lean_box(0);
    v___x_4300_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(
        v_f_4296_,
        v___x_4299_,
        v_init_4297_,
        v_x_4298_,
    );
    return v___x_4300_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfo(
    mut v_00_u03b1_4301_: *mut LeanObject,
    mut v_f_4302_: *mut LeanObject,
    mut v_init_4303_: *mut LeanObject,
    mut v_x_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    v___x_4305_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v_f_4302_, v_init_4303_, v_x_4304_);
    return v___x_4305_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(
    mut v___f_4306_: *mut LeanObject,
    mut v_a_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    v___x_4308_ = lean_apply_1(v___f_4306_, v_a_4307_);
    return v___x_4308_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(
    mut v_ctx_x3f_4309_: *mut LeanObject,
    mut v_i_4310_: *mut LeanObject,
    mut v_inst_4311_: *mut LeanObject,
    mut v_f_4312_: *mut LeanObject,
    mut v_children_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4315_: *mut LeanObject = core::ptr::null_mut();
    v_res_4315_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(
            v_ctx_x3f_4309_,
            v_i_4310_,
            v_inst_4311_,
            v_f_4312_,
            v_children_4313_,
            v_a_4314_,
        );
    lean_dec_ref(v_i_4310_);
    return v_res_4315_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(
    mut v_inst_4316_: *mut LeanObject,
    mut v_f_4317_: *mut LeanObject,
    mut v_ctx_x3f_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
    mut v_x_4320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4320_) {
                0 => {
                    v_i_4321_ = lean_ctor_get(v_x_4320_, 0);
                    lean_inc_ref(v_i_4321_);
                    v_t_4322_ = lean_ctor_get(v_x_4320_, 1);
                    lean_inc_ref(v_t_4322_);
                    lean_dec_ref_known(v_x_4320_, 2);
                    v___x_4323_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_4321_,
                        v_ctx_x3f_4318_,
                    );
                    v_ctx_x3f_4318_ = v___x_4323_;
                    v_x_4320_ = v_t_4322_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_toApplicative_4325_ = lean_ctor_get(v_inst_4316_, 0);
                    v_toBind_4326_ = lean_ctor_get(v_inst_4316_, 1);
                    lean_inc(v_toBind_4326_);
                    v_toPure_4327_ = lean_ctor_get(v_toApplicative_4325_, 1);
                    lean_inc(v_toPure_4327_);
                    v_i_4328_ = lean_ctor_get(v_x_4320_, 0);
                    lean_inc_ref_n(v_i_4328_, 2);
                    v_children_4329_ = lean_ctor_get(v_x_4320_, 1);
                    lean_inc_ref(v_children_4329_);
                    lean_dec_ref_known(v_x_4320_, 2);
                    lean_inc(v_f_4317_);
                    lean_inc(v_ctx_x3f_4318_);
                    v___f_4330_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
                    lean_closure_set(v___f_4330_, 0, v_ctx_x3f_4318_);
                    lean_closure_set(v___f_4330_, 1, v_i_4328_);
                    lean_closure_set(v___f_4330_, 2, v_inst_4316_);
                    lean_closure_set(v___f_4330_, 3, v_f_4317_);
                    lean_closure_set(v___f_4330_, 4, v_children_4329_);
                    if lean_obj_tag(v_ctx_x3f_4318_) == 0 {
                        lean_dec_ref(v_i_4328_);
                        lean_dec(v_f_4317_);
                        v___f_4331_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_4331_, 0, v___f_4330_);
                        v___x_4332_ = lean_apply_2(v_toPure_4327_, lean_box(0), v_a_4319_);
                        v___x_4333_ = lean_apply_4(
                            v_toBind_4326_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4332_,
                            v___f_4331_,
                        );
                        return v___x_4333_;
                    } else {
                        lean_dec(v_toPure_4327_);
                        v_val_4334_ = lean_ctor_get(v_ctx_x3f_4318_, 0);
                        lean_inc(v_val_4334_);
                        lean_dec_ref_known(v_ctx_x3f_4318_, 1);
                        v___f_4335_ = lean_alloc_closure(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_4335_, 0, v___f_4330_);
                        v___x_4336_ = lean_apply_3(v_f_4317_, v_val_4334_, v_i_4328_, v_a_4319_);
                        v___x_4337_ = lean_apply_4(
                            v_toBind_4326_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4336_,
                            v___f_4335_,
                        );
                        return v___x_4337_;
                    }
                }
                _ => {
                    v_toApplicative_4338_ = lean_ctor_get(v_inst_4316_, 0);
                    lean_inc_ref(v_toApplicative_4338_);
                    lean_dec_ref_known(v_x_4320_, 1);
                    lean_dec(v_ctx_x3f_4318_);
                    lean_dec(v_f_4317_);
                    lean_dec_ref(v_inst_4316_);
                    v_toPure_4339_ = lean_ctor_get(v_toApplicative_4338_, 1);
                    lean_inc(v_toPure_4339_);
                    lean_dec_ref(v_toApplicative_4338_);
                    v___x_4340_ = lean_apply_2(v_toPure_4339_, lean_box(0), v_a_4319_);
                    return v___x_4340_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(
    mut v_ctx_x3f_4341_: *mut LeanObject,
    mut v_i_4342_: *mut LeanObject,
    mut v_inst_4343_: *mut LeanObject,
    mut v_f_4344_: *mut LeanObject,
    mut v_children_4345_: *mut LeanObject,
    mut v_a_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    v___x_4347_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_4341_, v_i_4342_);
    lean_inc_ref(v_inst_4343_);
    v___x_4348_ = lean_alloc_closure(
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_4348_, 0, v_inst_4343_);
    lean_closure_set(v___x_4348_, 1, v_f_4344_);
    lean_closure_set(v___x_4348_, 2, v___x_4347_);
    v___x_4349_ = lean_unsigned_to_nat(0);
    v___x_4350_ = l_Lean_PersistentArray_foldlM___redArg(
        v_inst_4343_,
        v_children_4345_,
        v___x_4348_,
        v_a_4346_,
        v___x_4349_,
    );
    return v___x_4350_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go(
    mut v_m_4351_: *mut LeanObject,
    mut v_00_u03b1_4352_: *mut LeanObject,
    mut v_inst_4353_: *mut LeanObject,
    mut v_f_4354_: *mut LeanObject,
    mut v_ctx_x3f_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
    mut v_x_4357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    v___x_4358_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(
        v_inst_4353_,
        v_f_4354_,
        v_ctx_x3f_4355_,
        v_a_4356_,
        v_x_4357_,
    );
    return v___x_4358_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM___redArg(
    mut v_inst_4359_: *mut LeanObject,
    mut v_f_4360_: *mut LeanObject,
    mut v_init_4361_: *mut LeanObject,
    mut v_x_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ = lean_box(0);
    v___x_4364_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(
        v_inst_4359_,
        v_f_4360_,
        v___x_4363_,
        v_init_4361_,
        v_x_4362_,
    );
    return v___x_4364_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoM(
    mut v_m_4365_: *mut LeanObject,
    mut v_00_u03b1_4366_: *mut LeanObject,
    mut v_inst_4367_: *mut LeanObject,
    mut v_f_4368_: *mut LeanObject,
    mut v_init_4369_: *mut LeanObject,
    mut v_x_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    v___x_4371_ =
        l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_4367_, v_f_4368_, v_init_4369_, v_x_4370_);
    return v___x_4371_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(
    mut v_f_4372_: *mut LeanObject,
    mut v___x_4373_: *mut LeanObject,
    mut v_x_4374_: *mut LeanObject,
    mut v_x_4375_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4374_) == 0 {
        let mut v_cs_4376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4379_: u8 = 0;
        v_cs_4376_ = lean_ctor_get(v_x_4374_, 0);
        v___x_4377_ = lean_unsigned_to_nat(0);
        v___x_4378_ = lean_array_get_size(v_cs_4376_);
        v___x_4379_ = lean_nat_dec_lt(v___x_4377_, v___x_4378_);
        if v___x_4379_ == 0 {
            lean_dec(v___x_4373_);
            lean_dec(v_f_4372_);
            return v_x_4375_;
        } else {
            let mut v___x_4380_: u8 = 0;
            v___x_4380_ = lean_nat_dec_le(v___x_4378_, v___x_4378_);
            if v___x_4380_ == 0 {
                if v___x_4379_ == 0 {
                    lean_dec(v___x_4373_);
                    lean_dec(v_f_4372_);
                    return v_x_4375_;
                } else {
                    let mut v___x_4381_: usize = 0;
                    let mut v___x_4382_: usize = 0;
                    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4381_ = 0usize;
                    v___x_4382_ = lean_usize_of_nat(v___x_4378_);
                    v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4372_, v___x_4373_, v_cs_4376_, v___x_4381_, v___x_4382_, v_x_4375_);
                    return v___x_4383_;
                }
            } else {
                let mut v___x_4384_: usize = 0;
                let mut v___x_4385_: usize = 0;
                let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
                v___x_4384_ = 0usize;
                v___x_4385_ = lean_usize_of_nat(v___x_4378_);
                v___x_4386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4372_, v___x_4373_, v_cs_4376_, v___x_4384_, v___x_4385_, v_x_4375_);
                return v___x_4386_;
            }
        }
    } else {
        let mut v_vs_4387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4390_: u8 = 0;
        v_vs_4387_ = lean_ctor_get(v_x_4374_, 0);
        v___x_4388_ = lean_unsigned_to_nat(0);
        v___x_4389_ = lean_array_get_size(v_vs_4387_);
        v___x_4390_ = lean_nat_dec_lt(v___x_4388_, v___x_4389_);
        if v___x_4390_ == 0 {
            lean_dec(v___x_4373_);
            lean_dec(v_f_4372_);
            return v_x_4375_;
        } else {
            let mut v___x_4391_: u8 = 0;
            v___x_4391_ = lean_nat_dec_le(v___x_4389_, v___x_4389_);
            if v___x_4391_ == 0 {
                if v___x_4390_ == 0 {
                    lean_dec(v___x_4373_);
                    lean_dec(v_f_4372_);
                    return v_x_4375_;
                } else {
                    let mut v___x_4392_: usize = 0;
                    let mut v___x_4393_: usize = 0;
                    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4392_ = 0usize;
                    v___x_4393_ = lean_usize_of_nat(v___x_4389_);
                    v___x_4394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4372_, v___x_4373_, v_vs_4387_, v___x_4392_, v___x_4393_, v_x_4375_);
                    return v___x_4394_;
                }
            } else {
                let mut v___x_4395_: usize = 0;
                let mut v___x_4396_: usize = 0;
                let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
                v___x_4395_ = 0usize;
                v___x_4396_ = lean_usize_of_nat(v___x_4389_);
                v___x_4397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4372_, v___x_4373_, v_vs_4387_, v___x_4395_, v___x_4396_, v_x_4375_);
                return v___x_4397_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(
    mut v_f_4398_: *mut LeanObject,
    mut v___x_4399_: *mut LeanObject,
    mut v_as_4400_: *mut LeanObject,
    mut v_i_4401_: usize,
    mut v_stop_4402_: usize,
    mut v_b_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4404_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: usize = 0;
    let mut v___x_4408_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4404_ = lean_usize_dec_eq(v_i_4401_, v_stop_4402_);
                if v___x_4404_ == 0 {
                    v___x_4405_ = lean_array_uget_borrowed(v_as_4400_, v_i_4401_);
                    lean_inc(v___x_4399_);
                    lean_inc(v_f_4398_);
                    v___x_4406_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_4398_, v___x_4399_, v___x_4405_, v_b_4403_);
                    v___x_4407_ = 1usize;
                    v___x_4408_ = lean_usize_add(v_i_4401_, v___x_4407_);
                    v_i_4401_ = v___x_4408_;
                    v_b_4403_ = v___x_4406_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_4399_);
                    lean_dec(v_f_4398_);
                    return v_b_4403_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(
    mut v_f_4410_: *mut LeanObject,
    mut v___x_4411_: *mut LeanObject,
    mut v_x_4412_: *mut LeanObject,
    mut v_x_4413_: usize,
    mut v_x_4414_: usize,
    mut v_x_4415_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4412_) == 0 {
        let mut v_cs_4416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: usize = 0;
        let mut v_j_4419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4421_: usize = 0;
        let mut v___x_4422_: usize = 0;
        let mut v___x_4423_: usize = 0;
        let mut v___x_4424_: usize = 0;
        let mut v___x_4425_: usize = 0;
        let mut v___x_4426_: usize = 0;
        let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4431_: u8 = 0;
        v_cs_4416_ = lean_ctor_get(v_x_4412_, 0);
        v___x_4417_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
        v___x_4418_ = lean_usize_shift_right(v_x_4413_, v_x_4414_);
        v_j_4419_ = lean_usize_to_nat(v___x_4418_);
        v___x_4420_ = lean_array_get_borrowed(v___x_4417_, v_cs_4416_, v_j_4419_);
        v___x_4421_ = 1usize;
        v___x_4422_ = lean_usize_shift_left(v___x_4421_, v_x_4414_);
        v___x_4423_ = lean_usize_sub(v___x_4422_, v___x_4421_);
        v___x_4424_ = lean_usize_land(v_x_4413_, v___x_4423_);
        v___x_4425_ = 5usize;
        v___x_4426_ = lean_usize_sub(v_x_4414_, v___x_4425_);
        lean_inc(v___x_4411_);
        lean_inc(v_f_4410_);
        v___x_4427_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_4410_, v___x_4411_, v___x_4420_, v___x_4424_, v___x_4426_, v_x_4415_);
        v___x_4428_ = lean_unsigned_to_nat(1);
        v___x_4429_ = lean_nat_add(v_j_4419_, v___x_4428_);
        lean_dec(v_j_4419_);
        v___x_4430_ = lean_array_get_size(v_cs_4416_);
        v___x_4431_ = lean_nat_dec_lt(v___x_4429_, v___x_4430_);
        if v___x_4431_ == 0 {
            lean_dec(v___x_4429_);
            lean_dec(v___x_4411_);
            lean_dec(v_f_4410_);
            return v___x_4427_;
        } else {
            let mut v___x_4432_: u8 = 0;
            v___x_4432_ = lean_nat_dec_le(v___x_4430_, v___x_4430_);
            if v___x_4432_ == 0 {
                if v___x_4431_ == 0 {
                    lean_dec(v___x_4429_);
                    lean_dec(v___x_4411_);
                    lean_dec(v_f_4410_);
                    return v___x_4427_;
                } else {
                    let mut v___x_4433_: usize = 0;
                    let mut v___x_4434_: usize = 0;
                    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4433_ = lean_usize_of_nat(v___x_4429_);
                    lean_dec(v___x_4429_);
                    v___x_4434_ = lean_usize_of_nat(v___x_4430_);
                    v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4410_, v___x_4411_, v_cs_4416_, v___x_4433_, v___x_4434_, v___x_4427_);
                    return v___x_4435_;
                }
            } else {
                let mut v___x_4436_: usize = 0;
                let mut v___x_4437_: usize = 0;
                let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
                v___x_4436_ = lean_usize_of_nat(v___x_4429_);
                lean_dec(v___x_4429_);
                v___x_4437_ = lean_usize_of_nat(v___x_4430_);
                v___x_4438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4410_, v___x_4411_, v_cs_4416_, v___x_4436_, v___x_4437_, v___x_4427_);
                return v___x_4438_;
            }
        }
    } else {
        let mut v_vs_4439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4442_: u8 = 0;
        v_vs_4439_ = lean_ctor_get(v_x_4412_, 0);
        v___x_4440_ = lean_usize_to_nat(v_x_4413_);
        v___x_4441_ = lean_array_get_size(v_vs_4439_);
        v___x_4442_ = lean_nat_dec_lt(v___x_4440_, v___x_4441_);
        if v___x_4442_ == 0 {
            lean_dec(v___x_4440_);
            lean_dec(v___x_4411_);
            lean_dec(v_f_4410_);
            return v_x_4415_;
        } else {
            let mut v___x_4443_: u8 = 0;
            v___x_4443_ = lean_nat_dec_le(v___x_4441_, v___x_4441_);
            if v___x_4443_ == 0 {
                if v___x_4442_ == 0 {
                    lean_dec(v___x_4440_);
                    lean_dec(v___x_4411_);
                    lean_dec(v_f_4410_);
                    return v_x_4415_;
                } else {
                    let mut v___x_4444_: usize = 0;
                    let mut v___x_4445_: usize = 0;
                    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4444_ = lean_usize_of_nat(v___x_4440_);
                    lean_dec(v___x_4440_);
                    v___x_4445_ = lean_usize_of_nat(v___x_4441_);
                    v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4410_, v___x_4411_, v_vs_4439_, v___x_4444_, v___x_4445_, v_x_4415_);
                    return v___x_4446_;
                }
            } else {
                let mut v___x_4447_: usize = 0;
                let mut v___x_4448_: usize = 0;
                let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
                v___x_4447_ = lean_usize_of_nat(v___x_4440_);
                lean_dec(v___x_4440_);
                v___x_4448_ = lean_usize_of_nat(v___x_4441_);
                v___x_4449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4410_, v___x_4411_, v_vs_4439_, v___x_4447_, v___x_4448_, v_x_4415_);
                return v___x_4449_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(
    mut v_f_4450_: *mut LeanObject,
    mut v___x_4451_: *mut LeanObject,
    mut v_t_4452_: *mut LeanObject,
    mut v_init_4453_: *mut LeanObject,
    mut v_start_4454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: u8 = 0;
    v___x_4455_ = lean_unsigned_to_nat(0);
    v___x_4456_ = lean_nat_dec_eq(v_start_4454_, v___x_4455_);
    if v___x_4456_ == 0 {
        let mut v_root_4457_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4458_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_4459_: usize = 0;
        let mut v_tailOff_4460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: u8 = 0;
        v_root_4457_ = lean_ctor_get(v_t_4452_, 0);
        v_tail_4458_ = lean_ctor_get(v_t_4452_, 1);
        v_shift_4459_ = lean_ctor_get_usize(v_t_4452_, 4);
        v_tailOff_4460_ = lean_ctor_get(v_t_4452_, 3);
        v___x_4461_ = lean_nat_dec_le(v_tailOff_4460_, v_start_4454_);
        if v___x_4461_ == 0 {
            let mut v___x_4462_: usize = 0;
            let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4465_: u8 = 0;
            v___x_4462_ = lean_usize_of_nat(v_start_4454_);
            lean_inc(v___x_4451_);
            lean_inc(v_f_4450_);
            v___x_4463_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_4450_, v___x_4451_, v_root_4457_, v___x_4462_, v_shift_4459_, v_init_4453_);
            v___x_4464_ = lean_array_get_size(v_tail_4458_);
            v___x_4465_ = lean_nat_dec_lt(v___x_4455_, v___x_4464_);
            if v___x_4465_ == 0 {
                lean_dec(v___x_4451_);
                lean_dec(v_f_4450_);
                return v___x_4463_;
            } else {
                let mut v___x_4466_: u8 = 0;
                v___x_4466_ = lean_nat_dec_le(v___x_4464_, v___x_4464_);
                if v___x_4466_ == 0 {
                    if v___x_4465_ == 0 {
                        lean_dec(v___x_4451_);
                        lean_dec(v_f_4450_);
                        return v___x_4463_;
                    } else {
                        let mut v___x_4467_: usize = 0;
                        let mut v___x_4468_: usize = 0;
                        let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4467_ = 0usize;
                        v___x_4468_ = lean_usize_of_nat(v___x_4464_);
                        v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4458_, v___x_4467_, v___x_4468_, v___x_4463_);
                        return v___x_4469_;
                    }
                } else {
                    let mut v___x_4470_: usize = 0;
                    let mut v___x_4471_: usize = 0;
                    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4470_ = 0usize;
                    v___x_4471_ = lean_usize_of_nat(v___x_4464_);
                    v___x_4472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4458_, v___x_4470_, v___x_4471_, v___x_4463_);
                    return v___x_4472_;
                }
            }
        } else {
            let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4475_: u8 = 0;
            v___x_4473_ = lean_nat_sub(v_start_4454_, v_tailOff_4460_);
            v___x_4474_ = lean_array_get_size(v_tail_4458_);
            v___x_4475_ = lean_nat_dec_lt(v___x_4473_, v___x_4474_);
            if v___x_4475_ == 0 {
                lean_dec(v___x_4473_);
                lean_dec(v___x_4451_);
                lean_dec(v_f_4450_);
                return v_init_4453_;
            } else {
                let mut v___x_4476_: u8 = 0;
                v___x_4476_ = lean_nat_dec_le(v___x_4474_, v___x_4474_);
                if v___x_4476_ == 0 {
                    if v___x_4475_ == 0 {
                        lean_dec(v___x_4473_);
                        lean_dec(v___x_4451_);
                        lean_dec(v_f_4450_);
                        return v_init_4453_;
                    } else {
                        let mut v___x_4477_: usize = 0;
                        let mut v___x_4478_: usize = 0;
                        let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4477_ = lean_usize_of_nat(v___x_4473_);
                        lean_dec(v___x_4473_);
                        v___x_4478_ = lean_usize_of_nat(v___x_4474_);
                        v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4458_, v___x_4477_, v___x_4478_, v_init_4453_);
                        return v___x_4479_;
                    }
                } else {
                    let mut v___x_4480_: usize = 0;
                    let mut v___x_4481_: usize = 0;
                    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4480_ = lean_usize_of_nat(v___x_4473_);
                    lean_dec(v___x_4473_);
                    v___x_4481_ = lean_usize_of_nat(v___x_4474_);
                    v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4458_, v___x_4480_, v___x_4481_, v_init_4453_);
                    return v___x_4482_;
                }
            }
        }
    } else {
        let mut v_root_4483_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4487_: u8 = 0;
        v_root_4483_ = lean_ctor_get(v_t_4452_, 0);
        v_tail_4484_ = lean_ctor_get(v_t_4452_, 1);
        lean_inc(v___x_4451_);
        lean_inc(v_f_4450_);
        v___x_4485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_4450_, v___x_4451_, v_root_4483_, v_init_4453_);
        v___x_4486_ = lean_array_get_size(v_tail_4484_);
        v___x_4487_ = lean_nat_dec_lt(v___x_4455_, v___x_4486_);
        if v___x_4487_ == 0 {
            lean_dec(v___x_4451_);
            lean_dec(v_f_4450_);
            return v___x_4485_;
        } else {
            let mut v___x_4488_: u8 = 0;
            v___x_4488_ = lean_nat_dec_le(v___x_4486_, v___x_4486_);
            if v___x_4488_ == 0 {
                if v___x_4487_ == 0 {
                    lean_dec(v___x_4451_);
                    lean_dec(v_f_4450_);
                    return v___x_4485_;
                } else {
                    let mut v___x_4489_: usize = 0;
                    let mut v___x_4490_: usize = 0;
                    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4489_ = 0usize;
                    v___x_4490_ = lean_usize_of_nat(v___x_4486_);
                    v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4484_, v___x_4489_, v___x_4490_, v___x_4485_);
                    return v___x_4491_;
                }
            } else {
                let mut v___x_4492_: usize = 0;
                let mut v___x_4493_: usize = 0;
                let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
                v___x_4492_ = 0usize;
                v___x_4493_ = lean_usize_of_nat(v___x_4486_);
                v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4450_, v___x_4451_, v_tail_4484_, v___x_4492_, v___x_4493_, v___x_4485_);
                return v___x_4494_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(
    mut v_f_4495_: *mut LeanObject,
    mut v_ctx_x3f_4496_: *mut LeanObject,
    mut v_a_4497_: *mut LeanObject,
    mut v_x_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4498_) {
                0 => {
                    v_i_4499_ = lean_ctor_get(v_x_4498_, 0);
                    lean_inc_ref(v_i_4499_);
                    v_t_4500_ = lean_ctor_get(v_x_4498_, 1);
                    lean_inc_ref(v_t_4500_);
                    lean_dec_ref_known(v_x_4498_, 2);
                    v___x_4501_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_4499_,
                        v_ctx_x3f_4496_,
                    );
                    v_ctx_x3f_4496_ = v___x_4501_;
                    v_x_4498_ = v_t_4500_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_4503_ = lean_ctor_get(v_x_4498_, 0);
                    lean_inc_ref(v_i_4503_);
                    v_children_4504_ = lean_ctor_get(v_x_4498_, 1);
                    lean_inc_ref(v_children_4504_);
                    if lean_obj_tag(v_ctx_x3f_4496_) == 0 {
                        lean_dec_ref_known(v_x_4498_, 2);
                        v___y_4506_ = v_a_4497_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4510_ = lean_ctor_get(v_ctx_x3f_4496_, 0);
                        lean_inc(v_f_4495_);
                        lean_inc(v_val_4510_);
                        v___x_4511_ = lean_apply_3(v_f_4495_, v_val_4510_, v_x_4498_, v_a_4497_);
                        v___y_4506_ = v___x_4511_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref_known(v_x_4498_, 1);
                    lean_dec(v_ctx_x3f_4496_);
                    lean_dec(v_f_4495_);
                    return v_a_4497_;
                }
            },
            1 => {
                v___x_4507_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_4496_, v_i_4503_);
                lean_dec_ref(v_i_4503_);
                v___x_4508_ = lean_unsigned_to_nat(0);
                v___x_4509_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_4495_, v___x_4507_, v_children_4504_, v___y_4506_, v___x_4508_);
                lean_dec_ref(v_children_4504_);
                return v___x_4509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(
    mut v_f_4512_: *mut LeanObject,
    mut v___x_4513_: *mut LeanObject,
    mut v_as_4514_: *mut LeanObject,
    mut v_i_4515_: usize,
    mut v_stop_4516_: usize,
    mut v_b_4517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: usize = 0;
    let mut v___x_4522_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4518_ = lean_usize_dec_eq(v_i_4515_, v_stop_4516_);
                if v___x_4518_ == 0 {
                    v___x_4519_ = lean_array_uget_borrowed(v_as_4514_, v_i_4515_);
                    lean_inc(v___x_4519_);
                    lean_inc(v___x_4513_);
                    lean_inc(v_f_4512_);
                    v___x_4520_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_4512_, v___x_4513_, v_b_4517_, v___x_4519_);
                    v___x_4521_ = 1usize;
                    v___x_4522_ = lean_usize_add(v_i_4515_, v___x_4521_);
                    v_i_4515_ = v___x_4522_;
                    v_b_4517_ = v___x_4520_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_4513_);
                    lean_dec(v_f_4512_);
                    return v_b_4517_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(
    mut v_f_4524_: *mut LeanObject,
    mut v___x_4525_: *mut LeanObject,
    mut v_as_4526_: *mut LeanObject,
    mut v_i_4527_: *mut LeanObject,
    mut v_stop_4528_: *mut LeanObject,
    mut v_b_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4530_: usize = 0;
    let mut v_stop_boxed_4531_: usize = 0;
    let mut v_res_4532_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4530_ = lean_unbox_usize(v_i_4527_);
    lean_dec(v_i_4527_);
    v_stop_boxed_4531_ = lean_unbox_usize(v_stop_4528_);
    lean_dec(v_stop_4528_);
    v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4524_, v___x_4525_, v_as_4526_, v_i_boxed_4530_, v_stop_boxed_4531_, v_b_4529_);
    lean_dec_ref(v_as_4526_);
    return v_res_4532_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_4533_: *mut LeanObject,
    mut v___x_4534_: *mut LeanObject,
    mut v_as_4535_: *mut LeanObject,
    mut v_i_4536_: *mut LeanObject,
    mut v_stop_4537_: *mut LeanObject,
    mut v_b_4538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4539_: usize = 0;
    let mut v_stop_boxed_4540_: usize = 0;
    let mut v_res_4541_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4539_ = lean_unbox_usize(v_i_4536_);
    lean_dec(v_i_4536_);
    v_stop_boxed_4540_ = lean_unbox_usize(v_stop_4537_);
    lean_dec(v_stop_4537_);
    v_res_4541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4533_, v___x_4534_, v_as_4535_, v_i_boxed_4539_, v_stop_boxed_4540_, v_b_4538_);
    lean_dec_ref(v_as_4535_);
    return v_res_4541_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(
    mut v_f_4542_: *mut LeanObject,
    mut v___x_4543_: *mut LeanObject,
    mut v_x_4544_: *mut LeanObject,
    mut v_x_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4546_: *mut LeanObject = core::ptr::null_mut();
    v_res_4546_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_4542_, v___x_4543_, v_x_4544_, v_x_4545_);
    lean_dec_ref(v_x_4544_);
    return v_res_4546_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(
    mut v_f_4547_: *mut LeanObject,
    mut v___x_4548_: *mut LeanObject,
    mut v_x_4549_: *mut LeanObject,
    mut v_x_4550_: *mut LeanObject,
    mut v_x_4551_: *mut LeanObject,
    mut v_x_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1544__boxed_4553_: usize = 0;
    let mut v_x_1545__boxed_4554_: usize = 0;
    let mut v_res_4555_: *mut LeanObject = core::ptr::null_mut();
    v_x_1544__boxed_4553_ = lean_unbox_usize(v_x_4550_);
    lean_dec(v_x_4550_);
    v_x_1545__boxed_4554_ = lean_unbox_usize(v_x_4551_);
    lean_dec(v_x_4551_);
    v_res_4555_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_4547_, v___x_4548_, v_x_4549_, v_x_1544__boxed_4553_, v_x_1545__boxed_4554_, v_x_4552_);
    lean_dec_ref(v_x_4549_);
    return v_res_4555_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(
    mut v_f_4556_: *mut LeanObject,
    mut v___x_4557_: *mut LeanObject,
    mut v_t_4558_: *mut LeanObject,
    mut v_init_4559_: *mut LeanObject,
    mut v_start_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4561_: *mut LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_4556_, v___x_4557_, v_t_4558_, v_init_4559_, v_start_4560_);
    lean_dec(v_start_4560_);
    lean_dec_ref(v_t_4558_);
    return v_res_4561_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go(
    mut v_00_u03b1_4562_: *mut LeanObject,
    mut v_f_4563_: *mut LeanObject,
    mut v_ctx_x3f_4564_: *mut LeanObject,
    mut v_a_4565_: *mut LeanObject,
    mut v_x_4566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    v___x_4567_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(
        v_f_4563_,
        v_ctx_x3f_4564_,
        v_a_4565_,
        v_x_4566_,
    );
    return v___x_4567_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(
    mut v_00_u03b1_4568_: *mut LeanObject,
    mut v_f_4569_: *mut LeanObject,
    mut v___x_4570_: *mut LeanObject,
    mut v_t_4571_: *mut LeanObject,
    mut v_init_4572_: *mut LeanObject,
    mut v_start_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    v___x_4574_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_4569_, v___x_4570_, v_t_4571_, v_init_4572_, v_start_4573_);
    return v___x_4574_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(
    mut v_00_u03b1_4575_: *mut LeanObject,
    mut v_f_4576_: *mut LeanObject,
    mut v___x_4577_: *mut LeanObject,
    mut v_t_4578_: *mut LeanObject,
    mut v_init_4579_: *mut LeanObject,
    mut v_start_4580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4581_: *mut LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(v_00_u03b1_4575_, v_f_4576_, v___x_4577_, v_t_4578_, v_init_4579_, v_start_4580_);
    lean_dec(v_start_4580_);
    lean_dec_ref(v_t_4578_);
    return v_res_4581_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(
    mut v_00_u03b1_4582_: *mut LeanObject,
    mut v_f_4583_: *mut LeanObject,
    mut v___x_4584_: *mut LeanObject,
    mut v_x_4585_: *mut LeanObject,
    mut v_x_4586_: usize,
    mut v_x_4587_: usize,
    mut v_x_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    v___x_4589_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_4583_, v___x_4584_, v_x_4585_, v_x_4586_, v_x_4587_, v_x_4588_);
    return v___x_4589_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(
    mut v_00_u03b1_4590_: *mut LeanObject,
    mut v_f_4591_: *mut LeanObject,
    mut v___x_4592_: *mut LeanObject,
    mut v_x_4593_: *mut LeanObject,
    mut v_x_4594_: *mut LeanObject,
    mut v_x_4595_: *mut LeanObject,
    mut v_x_4596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1763__boxed_4597_: usize = 0;
    let mut v_x_1764__boxed_4598_: usize = 0;
    let mut v_res_4599_: *mut LeanObject = core::ptr::null_mut();
    v_x_1763__boxed_4597_ = lean_unbox_usize(v_x_4594_);
    lean_dec(v_x_4594_);
    v_x_1764__boxed_4598_ = lean_unbox_usize(v_x_4595_);
    lean_dec(v_x_4595_);
    v_res_4599_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(v_00_u03b1_4590_, v_f_4591_, v___x_4592_, v_x_4593_, v_x_1763__boxed_4597_, v_x_1764__boxed_4598_, v_x_4596_);
    lean_dec_ref(v_x_4593_);
    return v_res_4599_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(
    mut v_00_u03b1_4600_: *mut LeanObject,
    mut v_f_4601_: *mut LeanObject,
    mut v___x_4602_: *mut LeanObject,
    mut v_as_4603_: *mut LeanObject,
    mut v_i_4604_: usize,
    mut v_stop_4605_: usize,
    mut v_b_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_4601_, v___x_4602_, v_as_4603_, v_i_4604_, v_stop_4605_, v_b_4606_);
    return v___x_4607_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(
    mut v_00_u03b1_4608_: *mut LeanObject,
    mut v_f_4609_: *mut LeanObject,
    mut v___x_4610_: *mut LeanObject,
    mut v_as_4611_: *mut LeanObject,
    mut v_i_4612_: *mut LeanObject,
    mut v_stop_4613_: *mut LeanObject,
    mut v_b_4614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4615_: usize = 0;
    let mut v_stop_boxed_4616_: usize = 0;
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4615_ = lean_unbox_usize(v_i_4612_);
    lean_dec(v_i_4612_);
    v_stop_boxed_4616_ = lean_unbox_usize(v_stop_4613_);
    lean_dec(v_stop_4613_);
    v_res_4617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(v_00_u03b1_4608_, v_f_4609_, v___x_4610_, v_as_4611_, v_i_boxed_4615_, v_stop_boxed_4616_, v_b_4614_);
    lean_dec_ref(v_as_4611_);
    return v_res_4617_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(
    mut v_00_u03b1_4618_: *mut LeanObject,
    mut v_f_4619_: *mut LeanObject,
    mut v___x_4620_: *mut LeanObject,
    mut v_x_4621_: *mut LeanObject,
    mut v_x_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    v___x_4623_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_4619_, v___x_4620_, v_x_4621_, v_x_4622_);
    return v___x_4623_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(
    mut v_00_u03b1_4624_: *mut LeanObject,
    mut v_f_4625_: *mut LeanObject,
    mut v___x_4626_: *mut LeanObject,
    mut v_x_4627_: *mut LeanObject,
    mut v_x_4628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4629_: *mut LeanObject = core::ptr::null_mut();
    v_res_4629_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(v_00_u03b1_4624_, v_f_4625_, v___x_4626_, v_x_4627_, v_x_4628_);
    lean_dec_ref(v_x_4627_);
    return v_res_4629_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4630_: *mut LeanObject,
    mut v_f_4631_: *mut LeanObject,
    mut v___x_4632_: *mut LeanObject,
    mut v_as_4633_: *mut LeanObject,
    mut v_i_4634_: usize,
    mut v_stop_4635_: usize,
    mut v_b_4636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_4631_, v___x_4632_, v_as_4633_, v_i_4634_, v_stop_4635_, v_b_4636_);
    return v___x_4637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4638_: *mut LeanObject,
    mut v_f_4639_: *mut LeanObject,
    mut v___x_4640_: *mut LeanObject,
    mut v_as_4641_: *mut LeanObject,
    mut v_i_4642_: *mut LeanObject,
    mut v_stop_4643_: *mut LeanObject,
    mut v_b_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4645_: usize = 0;
    let mut v_stop_boxed_4646_: usize = 0;
    let mut v_res_4647_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4645_ = lean_unbox_usize(v_i_4642_);
    lean_dec(v_i_4642_);
    v_stop_boxed_4646_ = lean_unbox_usize(v_stop_4643_);
    lean_dec(v_stop_4643_);
    v_res_4647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(v_00_u03b1_4638_, v_f_4639_, v___x_4640_, v_as_4641_, v_i_boxed_4645_, v_stop_boxed_4646_, v_b_4644_);
    lean_dec_ref(v_as_4641_);
    return v_res_4647_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoTree___redArg(
    mut v_init_4648_: *mut LeanObject,
    mut v_f_4649_: *mut LeanObject,
    mut v_x_4650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    v___x_4651_ = lean_box(0);
    v___x_4652_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(
        v_f_4649_,
        v___x_4651_,
        v_init_4648_,
        v_x_4650_,
    );
    return v___x_4652_;
}
pub unsafe fn l_Lean_Elab_InfoTree_foldInfoTree(
    mut v_00_u03b1_4653_: *mut LeanObject,
    mut v_init_4654_: *mut LeanObject,
    mut v_f_4655_: *mut LeanObject,
    mut v_x_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    v___x_4657_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v_init_4654_, v_f_4655_, v_x_4656_);
    return v___x_4657_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(
    mut v_toPure_4658_: *mut LeanObject,
    mut v_result_4659_: *mut LeanObject,
    mut v_____do__lift_4660_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4660_) == 0 {
        let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
        v___x_4661_ = lean_apply_2(v_toPure_4658_, lean_box(0), v_result_4659_);
        return v___x_4661_;
    } else {
        let mut v_val_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
        v_val_4662_ = lean_ctor_get(v_____do__lift_4660_, 0);
        lean_inc(v_val_4662_);
        v___x_4663_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4663_, 0, v_val_4662_);
        lean_ctor_set(v___x_4663_, 1, v_result_4659_);
        v___x_4664_ = lean_apply_2(v_toPure_4658_, lean_box(0), v___x_4663_);
        return v___x_4664_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(
    mut v_toPure_4665_: *mut LeanObject,
    mut v_result_4666_: *mut LeanObject,
    mut v_____do__lift_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(
        v_toPure_4665_,
        v_result_4666_,
        v_____do__lift_4667_,
    );
    lean_dec(v_____do__lift_4667_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(
    mut v_toPure_4669_: *mut LeanObject,
    mut v_f_4670_: *mut LeanObject,
    mut v_toBind_4671_: *mut LeanObject,
    mut v_ctx_4672_: *mut LeanObject,
    mut v_info_4673_: *mut LeanObject,
    mut v_result_4674_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_info_4673_) == 1 {
        let mut v_i_4675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
        v_i_4675_ = lean_ctor_get(v_info_4673_, 0);
        lean_inc_ref(v_i_4675_);
        lean_dec_ref_known(v_info_4673_, 1);
        v___f_4676_ = lean_alloc_closure(
            l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_4676_, 0, v_toPure_4669_);
        lean_closure_set(v___f_4676_, 1, v_result_4674_);
        v___x_4677_ = lean_apply_2(v_f_4670_, v_ctx_4672_, v_i_4675_);
        v___x_4678_ = lean_apply_4(
            v_toBind_4671_,
            lean_box(0),
            lean_box(0),
            v___x_4677_,
            v___f_4676_,
        );
        return v___x_4678_;
    } else {
        let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_info_4673_);
        lean_dec_ref(v_ctx_4672_);
        lean_dec(v_toBind_4671_);
        lean_dec(v_f_4670_);
        v___x_4679_ = lean_apply_2(v_toPure_4669_, lean_box(0), v_result_4674_);
        return v___x_4679_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM___redArg(
    mut v_inst_4680_: *mut LeanObject,
    mut v_t_4681_: *mut LeanObject,
    mut v_f_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4683_ = lean_ctor_get(v_inst_4680_, 0);
    v_toBind_4684_ = lean_ctor_get(v_inst_4680_, 1);
    v_toPure_4685_ = lean_ctor_get(v_toApplicative_4683_, 1);
    lean_inc(v_toBind_4684_);
    lean_inc(v_toPure_4685_);
    v___f_4686_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4686_, 0, v_toPure_4685_);
    lean_closure_set(v___f_4686_, 1, v_f_4682_);
    lean_closure_set(v___f_4686_, 2, v_toBind_4684_);
    v___x_4687_ = lean_box(0);
    v___x_4688_ =
        l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_4680_, v___f_4686_, v___x_4687_, v_t_4681_);
    return v___x_4688_;
}
pub unsafe fn l_Lean_Elab_InfoTree_collectTermInfoM(
    mut v_m_4689_: *mut LeanObject,
    mut v_00_u03b1_4690_: *mut LeanObject,
    mut v_inst_4691_: *mut LeanObject,
    mut v_t_4692_: *mut LeanObject,
    mut v_f_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    v___x_4694_ =
        l_Lean_Elab_InfoTree_collectTermInfoM___redArg(v_inst_4691_, v_t_4692_, v_f_4693_);
    return v___x_4694_;
}
pub unsafe fn l_Lean_Elab_Info_isTerm(mut v_x_4695_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4695_) == 1 {
        let mut v___x_4696_: u8 = 0;
        v___x_4696_ = 1;
        return v___x_4696_;
    } else {
        let mut v___x_4697_: u8 = 0;
        v___x_4697_ = 0;
        return v___x_4697_;
    }
}
pub unsafe fn l_Lean_Elab_Info_isTerm___boxed(mut v_x_4698_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4699_: u8 = 0;
    let mut v_r_4700_: *mut LeanObject = core::ptr::null_mut();
    v_res_4699_ = l_Lean_Elab_Info_isTerm(v_x_4698_);
    lean_dec_ref(v_x_4698_);
    v_r_4700_ = lean_box((v_res_4699_) as usize);
    return v_r_4700_;
}
pub unsafe fn l_Lean_Elab_Info_isCompletion(mut v_x_4701_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4701_) == 8 {
        let mut v___x_4702_: u8 = 0;
        v___x_4702_ = 1;
        return v___x_4702_;
    } else {
        let mut v___x_4703_: u8 = 0;
        v___x_4703_ = 0;
        return v___x_4703_;
    }
}
pub unsafe fn l_Lean_Elab_Info_isCompletion___boxed(
    mut v_x_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4705_: u8 = 0;
    let mut v_r_4706_: *mut LeanObject = core::ptr::null_mut();
    v_res_4705_ = l_Lean_Elab_Info_isCompletion(v_x_4704_);
    lean_dec_ref(v_x_4704_);
    v_r_4706_ = lean_box((v_res_4705_) as usize);
    return v_r_4706_;
}
pub unsafe fn l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(
    mut v_ctx_4707_: *mut LeanObject,
    mut v_info_4708_: *mut LeanObject,
    mut v_result_4709_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_info_4708_) == 8 {
        let mut v_i_4710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
        v_i_4710_ = lean_ctor_get(v_info_4708_, 0);
        lean_inc_ref(v_i_4710_);
        v___x_4711_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4711_, 0, v_ctx_4707_);
        lean_ctor_set(v___x_4711_, 1, v_i_4710_);
        v___x_4712_ = lean_array_push(v_result_4709_, v___x_4711_);
        return v___x_4712_;
    } else {
        lean_dec_ref(v_ctx_4707_);
        return v_result_4709_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(
    mut v_ctx_4713_: *mut LeanObject,
    mut v_info_4714_: *mut LeanObject,
    mut v_result_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4716_: *mut LeanObject = core::ptr::null_mut();
    v_res_4716_ =
        l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(v_ctx_4713_, v_info_4714_, v_result_4715_);
    lean_dec_ref(v_info_4714_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_Elab_InfoTree_getCompletionInfos(
    mut v_infoTree_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    v___f_4721_ = l_Lean_Elab_InfoTree_getCompletionInfos___closed__0;
    v___x_4722_ = l_Lean_Elab_InfoTree_getCompletionInfos___closed__1;
    v___x_4723_ =
        l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_4721_, v___x_4722_, v_infoTree_4720_);
    return v___x_4723_;
}
pub unsafe fn l_Lean_Elab_Info_stx(mut v_x_4724_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4724_) {
        0 => {
            let mut v_i_4725_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toElabInfo_4726_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4727_: *mut LeanObject = core::ptr::null_mut();
            v_i_4725_ = lean_ctor_get(v_x_4724_, 0);
            v_toElabInfo_4726_ = lean_ctor_get(v_i_4725_, 0);
            v_stx_4727_ = lean_ctor_get(v_toElabInfo_4726_, 1);
            lean_inc(v_stx_4727_);
            return v_stx_4727_;
        }
        1 => {
            let mut v_i_4728_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toElabInfo_4729_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4730_: *mut LeanObject = core::ptr::null_mut();
            v_i_4728_ = lean_ctor_get(v_x_4724_, 0);
            v_toElabInfo_4729_ = lean_ctor_get(v_i_4728_, 0);
            v_stx_4730_ = lean_ctor_get(v_toElabInfo_4729_, 1);
            lean_inc(v_stx_4730_);
            return v_stx_4730_;
        }
        2 => {
            let mut v_i_4731_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toElabInfo_4732_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4733_: *mut LeanObject = core::ptr::null_mut();
            v_i_4731_ = lean_ctor_get(v_x_4724_, 0);
            v_toElabInfo_4732_ = lean_ctor_get(v_i_4731_, 0);
            v_stx_4733_ = lean_ctor_get(v_toElabInfo_4732_, 1);
            lean_inc(v_stx_4733_);
            return v_stx_4733_;
        }
        5 => {
            let mut v_i_4734_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4735_: *mut LeanObject = core::ptr::null_mut();
            v_i_4734_ = lean_ctor_get(v_x_4724_, 0);
            v_stx_4735_ = lean_ctor_get(v_i_4734_, 0);
            lean_inc(v_stx_4735_);
            return v_stx_4735_;
        }
        6 => {
            let mut v_i_4736_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4737_: *mut LeanObject = core::ptr::null_mut();
            v_i_4736_ = lean_ctor_get(v_x_4724_, 0);
            v_stx_4737_ = lean_ctor_get(v_i_4736_, 0);
            lean_inc(v_stx_4737_);
            return v_stx_4737_;
        }
        7 => {
            let mut v_i_4738_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4739_: *mut LeanObject = core::ptr::null_mut();
            v_i_4738_ = lean_ctor_get(v_x_4724_, 0);
            v_stx_4739_ = lean_ctor_get(v_i_4738_, 4);
            lean_inc(v_stx_4739_);
            return v_stx_4739_;
        }
        8 => {
            let mut v_i_4740_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
            v_i_4740_ = lean_ctor_get(v_x_4724_, 0);
            v___x_4741_ = l_Lean_Elab_CompletionInfo_stx(v_i_4740_);
            return v___x_4741_;
        }
        10 => {
            let mut v_i_4742_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4743_: *mut LeanObject = core::ptr::null_mut();
            v_i_4742_ = lean_ctor_get(v_x_4724_, 0);
            v_stx_4743_ = lean_ctor_get(v_i_4742_, 0);
            lean_inc(v_stx_4743_);
            return v_stx_4743_;
        }
        11 => {
            let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
            v___x_4744_ = lean_box(0);
            return v___x_4744_;
        }
        12 => {
            let mut v_i_4745_: *mut LeanObject = core::ptr::null_mut();
            v_i_4745_ = lean_ctor_get(v_x_4724_, 0);
            lean_inc(v_i_4745_);
            return v_i_4745_;
        }
        13 => {
            let mut v_i_4746_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toTermInfo_4747_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toElabInfo_4748_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4749_: *mut LeanObject = core::ptr::null_mut();
            v_i_4746_ = lean_ctor_get(v_x_4724_, 0);
            v_toTermInfo_4747_ = lean_ctor_get(v_i_4746_, 0);
            v_toElabInfo_4748_ = lean_ctor_get(v_toTermInfo_4747_, 0);
            v_stx_4749_ = lean_ctor_get(v_toElabInfo_4748_, 1);
            lean_inc(v_stx_4749_);
            return v_stx_4749_;
        }
        16 => {
            let mut v_i_4750_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toElabInfo_4751_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4752_: *mut LeanObject = core::ptr::null_mut();
            v_i_4750_ = lean_ctor_get(v_x_4724_, 0);
            v_toElabInfo_4751_ = lean_ctor_get(v_i_4750_, 0);
            v_stx_4752_ = lean_ctor_get(v_toElabInfo_4751_, 1);
            lean_inc(v_stx_4752_);
            return v_stx_4752_;
        }
        _ => {
            let mut v_i_4753_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stx_4754_: *mut LeanObject = core::ptr::null_mut();
            v_i_4753_ = lean_ctor_get(v_x_4724_, 0);
            v_stx_4754_ = lean_ctor_get(v_i_4753_, 1);
            lean_inc(v_stx_4754_);
            return v_stx_4754_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_stx___boxed(mut v_x_4755_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4756_: *mut LeanObject = core::ptr::null_mut();
    v_res_4756_ = l_Lean_Elab_Info_stx(v_x_4755_);
    lean_dec_ref(v_x_4755_);
    return v_res_4756_;
}
pub unsafe fn l_Lean_Elab_Info_lctx(mut v_x_4757_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4757_) {
        1 => {
            let mut v_i_4758_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lctx_4759_: *mut LeanObject = core::ptr::null_mut();
            v_i_4758_ = lean_ctor_get(v_x_4757_, 0);
            v_lctx_4759_ = lean_ctor_get(v_i_4758_, 1);
            lean_inc_ref(v_lctx_4759_);
            return v_lctx_4759_;
        }
        7 => {
            let mut v_i_4760_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lctx_4761_: *mut LeanObject = core::ptr::null_mut();
            v_i_4760_ = lean_ctor_get(v_x_4757_, 0);
            v_lctx_4761_ = lean_ctor_get(v_i_4760_, 2);
            lean_inc_ref(v_lctx_4761_);
            return v_lctx_4761_;
        }
        13 => {
            let mut v_i_4762_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toTermInfo_4763_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lctx_4764_: *mut LeanObject = core::ptr::null_mut();
            v_i_4762_ = lean_ctor_get(v_x_4757_, 0);
            v_toTermInfo_4763_ = lean_ctor_get(v_i_4762_, 0);
            v_lctx_4764_ = lean_ctor_get(v_toTermInfo_4763_, 1);
            lean_inc_ref(v_lctx_4764_);
            return v_lctx_4764_;
        }
        4 => {
            let mut v_i_4765_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lctx_4766_: *mut LeanObject = core::ptr::null_mut();
            v_i_4765_ = lean_ctor_get(v_x_4757_, 0);
            v_lctx_4766_ = lean_ctor_get(v_i_4765_, 0);
            lean_inc_ref(v_lctx_4766_);
            return v_lctx_4766_;
        }
        8 => {
            let mut v_i_4767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
            v_i_4767_ = lean_ctor_get(v_x_4757_, 0);
            v___x_4768_ = l_Lean_Elab_CompletionInfo_lctx(v_i_4767_);
            return v___x_4768_;
        }
        _ => {
            let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
            v___x_4769_ = l_Lean_LocalContext_empty;
            return v___x_4769_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_lctx___boxed(mut v_x_4770_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4771_: *mut LeanObject = core::ptr::null_mut();
    v_res_4771_ = l_Lean_Elab_Info_lctx(v_x_4770_);
    lean_dec_ref(v_x_4770_);
    return v_res_4771_;
}
pub unsafe fn l_Lean_Elab_Info_pos_x3f(mut v_i_4772_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    v___x_4773_ = l_Lean_Elab_Info_stx(v_i_4772_);
    v___x_4774_ = 1;
    v___x_4775_ = l_Lean_Syntax_getPos_x3f(v___x_4773_, v___x_4774_);
    lean_dec(v___x_4773_);
    return v___x_4775_;
}
pub unsafe fn l_Lean_Elab_Info_pos_x3f___boxed(mut v_i_4776_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4777_: *mut LeanObject = core::ptr::null_mut();
    v_res_4777_ = l_Lean_Elab_Info_pos_x3f(v_i_4776_);
    lean_dec_ref(v_i_4776_);
    return v_res_4777_;
}
pub unsafe fn l_Lean_Elab_Info_tailPos_x3f(mut v_i_4778_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    v___x_4779_ = l_Lean_Elab_Info_stx(v_i_4778_);
    v___x_4780_ = 1;
    v___x_4781_ = l_Lean_Syntax_getTailPos_x3f(v___x_4779_, v___x_4780_);
    lean_dec(v___x_4779_);
    return v___x_4781_;
}
pub unsafe fn l_Lean_Elab_Info_tailPos_x3f___boxed(
    mut v_i_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Elab_Info_tailPos_x3f(v_i_4782_);
    lean_dec_ref(v_i_4782_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_Elab_Info_range_x3f(mut v_i_4784_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    v___x_4785_ = l_Lean_Elab_Info_stx(v_i_4784_);
    v___x_4786_ = 1;
    v___x_4787_ = l_Lean_Syntax_getRange_x3f(v___x_4785_, v___x_4786_);
    lean_dec(v___x_4785_);
    return v___x_4787_;
}
pub unsafe fn l_Lean_Elab_Info_range_x3f___boxed(
    mut v_i_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4789_: *mut LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Lean_Elab_Info_range_x3f(v_i_4788_);
    lean_dec_ref(v_i_4788_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_Elab_Info_contains(
    mut v_i_4790_: *mut LeanObject,
    mut v_pos_4791_: *mut LeanObject,
    mut v_includeStop_4792_: u8,
) -> u8 {
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___x_4793_ = l_Lean_Elab_Info_range_x3f(v_i_4790_);
    if lean_obj_tag(v___x_4793_) == 0 {
        let mut v___x_4794_: u8 = 0;
        v___x_4794_ = 0;
        return v___x_4794_;
    } else {
        let mut v_val_4795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4796_: u8 = 0;
        v_val_4795_ = lean_ctor_get(v___x_4793_, 0);
        lean_inc(v_val_4795_);
        lean_dec_ref_known(v___x_4793_, 1);
        v___x_4796_ = l_Lean_Syntax_Range_contains(v_val_4795_, v_pos_4791_, v_includeStop_4792_);
        lean_dec(v_val_4795_);
        return v___x_4796_;
    }
}
pub unsafe fn l_Lean_Elab_Info_contains___boxed(
    mut v_i_4797_: *mut LeanObject,
    mut v_pos_4798_: *mut LeanObject,
    mut v_includeStop_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_4800_: u8 = 0;
    let mut v_res_4801_: u8 = 0;
    let mut v_r_4802_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_4800_ = (lean_unbox(v_includeStop_4799_) as u8);
    v_res_4801_ = l_Lean_Elab_Info_contains(v_i_4797_, v_pos_4798_, v_includeStop_boxed_4800_);
    lean_dec(v_pos_4798_);
    lean_dec_ref(v_i_4797_);
    v_r_4802_ = lean_box((v_res_4801_) as usize);
    return v_r_4802_;
}
pub unsafe fn l_Lean_Elab_Info_size_x3f(mut v_i_4803_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4804_ = l_Lean_Elab_Info_pos_x3f(v_i_4803_);
                if lean_obj_tag(v___x_4804_) == 0 {
                    return v___x_4804_;
                } else {
                    v_val_4805_ = lean_ctor_get(v___x_4804_, 0);
                    lean_inc(v_val_4805_);
                    lean_dec_ref_known(v___x_4804_, 1);
                    v___x_4806_ = l_Lean_Elab_Info_tailPos_x3f(v_i_4803_);
                    if lean_obj_tag(v___x_4806_) == 0 {
                        lean_dec(v_val_4805_);
                        return v___x_4806_;
                    } else {
                        v_val_4807_ = lean_ctor_get(v___x_4806_, 0);
                        v_isSharedCheck_4815_ = (!lean_is_exclusive(v___x_4806_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v___x_4809_ = v___x_4806_;
                            v_isShared_4810_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_4807_);
                            lean_dec(v___x_4806_);
                            v___x_4809_ = lean_box(0);
                            v_isShared_4810_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4811_ = lean_nat_sub(v_val_4807_, v_val_4805_);
                lean_dec(v_val_4805_);
                lean_dec(v_val_4807_);
                if v_isShared_4810_ == 0 {
                    lean_ctor_set(v___x_4809_, 0, v___x_4811_);
                    v___x_4813_ = v___x_4809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
                    v___x_4813_ = v_reuseFailAlloc_4814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_size_x3f___boxed(mut v_i_4816_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4817_: *mut LeanObject = core::ptr::null_mut();
    v_res_4817_ = l_Lean_Elab_Info_size_x3f(v_i_4816_);
    lean_dec_ref(v_i_4816_);
    return v_res_4817_;
}
pub unsafe fn l_Lean_Elab_Info_isSmaller(
    mut v_i_u2081_4818_: *mut LeanObject,
    mut v_i_u2082_4819_: *mut LeanObject,
) -> u8 {
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    v___x_4820_ = l_Lean_Elab_Info_size_x3f(v_i_u2081_4818_);
    if lean_obj_tag(v___x_4820_) == 1 {
        let mut v_val_4821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
        v_val_4821_ = lean_ctor_get(v___x_4820_, 0);
        lean_inc(v_val_4821_);
        lean_dec_ref_known(v___x_4820_, 1);
        v___x_4822_ = l_Lean_Elab_Info_size_x3f(v_i_u2082_4819_);
        if lean_obj_tag(v___x_4822_) == 0 {
            let mut v___x_4823_: u8 = 0;
            lean_dec(v_val_4821_);
            v___x_4823_ = 1;
            return v___x_4823_;
        } else {
            let mut v_val_4824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4825_: u8 = 0;
            v_val_4824_ = lean_ctor_get(v___x_4822_, 0);
            lean_inc(v_val_4824_);
            lean_dec_ref_known(v___x_4822_, 1);
            v___x_4825_ = lean_nat_dec_lt(v_val_4821_, v_val_4824_);
            lean_dec(v_val_4824_);
            lean_dec(v_val_4821_);
            return v___x_4825_;
        }
    } else {
        let mut v___x_4826_: u8 = 0;
        lean_dec(v___x_4820_);
        v___x_4826_ = 0;
        return v___x_4826_;
    }
}
pub unsafe fn l_Lean_Elab_Info_isSmaller___boxed(
    mut v_i_u2081_4827_: *mut LeanObject,
    mut v_i_u2082_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4829_: u8 = 0;
    let mut v_r_4830_: *mut LeanObject = core::ptr::null_mut();
    v_res_4829_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_4827_, v_i_u2082_4828_);
    lean_dec_ref(v_i_u2082_4828_);
    lean_dec_ref(v_i_u2081_4827_);
    v_r_4830_ = lean_box((v_res_4829_) as usize);
    return v_r_4830_;
}
pub unsafe fn l_Lean_Elab_Info_occursInside_x3f(
    mut v_i_4831_: *mut LeanObject,
    mut v_hoverPos_4832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___y_4839_: u8 = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: u8 = 0;
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4833_ = l_Lean_Elab_Info_pos_x3f(v_i_4831_);
                if lean_obj_tag(v___x_4833_) == 0 {
                    return v___x_4833_;
                } else {
                    v_val_4834_ = lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4836_ = v___x_4833_;
                        v_isShared_4837_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4834_);
                        lean_dec(v___x_4833_);
                        v___x_4836_ = lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4845_ = l_Lean_Elab_Info_tailPos_x3f(v_i_4831_);
                if lean_obj_tag(v___x_4845_) == 0 {
                    lean_del_object(v___x_4836_);
                    lean_dec(v_val_4834_);
                    return v___x_4845_;
                } else {
                    v_val_4846_ = lean_ctor_get(v___x_4845_, 0);
                    lean_inc(v_val_4846_);
                    lean_dec_ref_known(v___x_4845_, 1);
                    v___x_4847_ = lean_nat_dec_le(v_val_4834_, v_hoverPos_4832_);
                    if v___x_4847_ == 0 {
                        lean_dec(v_val_4846_);
                        v___y_4839_ = v___x_4847_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4848_ = lean_nat_dec_lt(v_hoverPos_4832_, v_val_4846_);
                        lean_dec(v_val_4846_);
                        v___y_4839_ = v___x_4848_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_4839_ == 0 {
                    lean_del_object(v___x_4836_);
                    lean_dec(v_val_4834_);
                    v___x_4840_ = lean_box(0);
                    return v___x_4840_;
                } else {
                    v___x_4841_ = lean_nat_sub(v_hoverPos_4832_, v_val_4834_);
                    lean_dec(v_val_4834_);
                    if v_isShared_4837_ == 0 {
                        lean_ctor_set(v___x_4836_, 0, v___x_4841_);
                        v___x_4843_ = v___x_4836_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4841_);
                        v___x_4843_ = v_reuseFailAlloc_4844_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_occursInside_x3f___boxed(
    mut v_i_4850_: *mut LeanObject,
    mut v_hoverPos_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4852_: *mut LeanObject = core::ptr::null_mut();
    v_res_4852_ = l_Lean_Elab_Info_occursInside_x3f(v_i_4850_, v_hoverPos_4851_);
    lean_dec(v_hoverPos_4851_);
    lean_dec_ref(v_i_4850_);
    return v_res_4852_;
}
pub unsafe fn l_Lean_Elab_Info_occursInOrOnBoundary(
    mut v_i_4853_: *mut LeanObject,
    mut v_hoverPos_4854_: *mut LeanObject,
) -> u8 {
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    v___x_4855_ = l_Lean_Elab_Info_pos_x3f(v_i_4853_);
    if lean_obj_tag(v___x_4855_) == 1 {
        let mut v_val_4856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
        v_val_4856_ = lean_ctor_get(v___x_4855_, 0);
        lean_inc(v_val_4856_);
        lean_dec_ref_known(v___x_4855_, 1);
        v___x_4857_ = l_Lean_Elab_Info_tailPos_x3f(v_i_4853_);
        if lean_obj_tag(v___x_4857_) == 1 {
            let mut v_val_4858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4859_: u8 = 0;
            v_val_4858_ = lean_ctor_get(v___x_4857_, 0);
            lean_inc(v_val_4858_);
            lean_dec_ref_known(v___x_4857_, 1);
            v___x_4859_ = lean_nat_dec_le(v_val_4856_, v_hoverPos_4854_);
            lean_dec(v_val_4856_);
            if v___x_4859_ == 0 {
                lean_dec(v_val_4858_);
                return v___x_4859_;
            } else {
                let mut v___x_4860_: u8 = 0;
                v___x_4860_ = lean_nat_dec_le(v_hoverPos_4854_, v_val_4858_);
                lean_dec(v_val_4858_);
                return v___x_4860_;
            }
        } else {
            let mut v___x_4861_: u8 = 0;
            lean_dec(v___x_4857_);
            lean_dec(v_val_4856_);
            v___x_4861_ = 0;
            return v___x_4861_;
        }
    } else {
        let mut v___x_4862_: u8 = 0;
        lean_dec(v___x_4855_);
        v___x_4862_ = 0;
        return v___x_4862_;
    }
}
pub unsafe fn l_Lean_Elab_Info_occursInOrOnBoundary___boxed(
    mut v_i_4863_: *mut LeanObject,
    mut v_hoverPos_4864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4865_: u8 = 0;
    let mut v_r_4866_: *mut LeanObject = core::ptr::null_mut();
    v_res_4865_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_4863_, v_hoverPos_4864_);
    lean_dec(v_hoverPos_4864_);
    lean_dec_ref(v_i_4863_);
    v_r_4866_ = lean_box((v_res_4865_) as usize);
    return v_r_4866_;
}
pub unsafe fn l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(
    mut v_p_4867_: *mut LeanObject,
    mut v_ctx_4868_: *mut LeanObject,
    mut v_i_4869_: *mut LeanObject,
    mut v_x_4870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    lean_inc_ref(v_i_4869_);
    v___x_4871_ = lean_apply_1(v_p_4867_, v_i_4869_);
    v___x_4872_ = (lean_unbox(v___x_4871_) as u8);
    if v___x_4872_ == 0 {
        let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_i_4869_);
        lean_dec_ref(v_ctx_4868_);
        v___x_4873_ = lean_box(0);
        return v___x_4873_;
    } else {
        let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
        v___x_4874_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4874_, 0, v_ctx_4868_);
        lean_ctor_set(v___x_4874_, 1, v_i_4869_);
        v___x_4875_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4875_, 0, v___x_4874_);
        return v___x_4875_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(
    mut v_p_4876_: *mut LeanObject,
    mut v_ctx_4877_: *mut LeanObject,
    mut v_i_4878_: *mut LeanObject,
    mut v_x_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4880_: *mut LeanObject = core::ptr::null_mut();
    v_res_4880_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(
        v_p_4876_,
        v_ctx_4877_,
        v_i_4878_,
        v_x_4879_,
    );
    lean_dec_ref(v_x_4879_);
    return v_res_4880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(
    mut v_as_4881_: *mut LeanObject,
    mut v_i_4882_: usize,
    mut v_stop_4883_: usize,
    mut v_b_4884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: usize = 0;
    let mut v___x_4888_: usize = 0;
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4890_ = lean_usize_dec_eq(v_i_4882_, v_stop_4883_);
                if v___x_4890_ == 0 {
                    v___x_4891_ = lean_array_uget_borrowed(v_as_4881_, v_i_4882_);
                    v_fst_4892_ = lean_ctor_get(v___x_4891_, 0);
                    v_fst_4893_ = lean_ctor_get(v_b_4884_, 0);
                    v___x_4894_ = lean_nat_dec_lt(v_fst_4892_, v_fst_4893_);
                    if v___x_4894_ == 0 {
                        v___y_4886_ = v_b_4884_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4886_ = v___x_4891_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_b_4884_);
                    return v_b_4884_;
                }
            }
            1 => {
                v___x_4887_ = 1usize;
                v___x_4888_ = lean_usize_add(v_i_4882_, v___x_4887_);
                v_i_4882_ = v___x_4888_;
                v_b_4884_ = v___y_4886_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(
    mut v_as_4895_: *mut LeanObject,
    mut v_i_4896_: *mut LeanObject,
    mut v_stop_4897_: *mut LeanObject,
    mut v_b_4898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4899_: usize = 0;
    let mut v_stop_boxed_4900_: usize = 0;
    let mut v_res_4901_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4899_ = lean_unbox_usize(v_i_4896_);
    lean_dec(v_i_4896_);
    v_stop_boxed_4900_ = lean_unbox_usize(v_stop_4897_);
    lean_dec(v_stop_4897_);
    v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_4895_, v_i_boxed_4899_, v_stop_boxed_4900_, v_b_4898_);
    lean_dec_ref(v_b_4898_);
    lean_dec_ref(v_as_4895_);
    return v_res_4901_;
}
pub unsafe fn l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(
    mut v_as_4902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: u8 = 0;
    v___x_4903_ = lean_unsigned_to_nat(0);
    v___x_4904_ = lean_array_get_size(v_as_4902_);
    v___x_4905_ = lean_nat_dec_lt(v___x_4903_, v___x_4904_);
    if v___x_4905_ == 0 {
        let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
        v___x_4906_ = lean_box(0);
        return v___x_4906_;
    } else {
        let mut v_a0_4907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4909_: u8 = 0;
        v_a0_4907_ = lean_array_fget_borrowed(v_as_4902_, v___x_4903_);
        v___x_4908_ = lean_unsigned_to_nat(1);
        v___x_4909_ = lean_nat_dec_lt(v___x_4908_, v___x_4904_);
        if v___x_4909_ == 0 {
            let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_a0_4907_);
            v___x_4910_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4910_, 0, v_a0_4907_);
            return v___x_4910_;
        } else {
            let mut v___x_4911_: u8 = 0;
            v___x_4911_ = lean_nat_dec_le(v___x_4904_, v___x_4904_);
            if v___x_4911_ == 0 {
                if v___x_4909_ == 0 {
                    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v_a0_4907_);
                    v___x_4912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4912_, 0, v_a0_4907_);
                    return v___x_4912_;
                } else {
                    let mut v___x_4913_: usize = 0;
                    let mut v___x_4914_: usize = 0;
                    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4913_ = 1usize;
                    v___x_4914_ = lean_usize_of_nat(v___x_4904_);
                    v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_4902_, v___x_4913_, v___x_4914_, v_a0_4907_);
                    v___x_4916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4916_, 0, v___x_4915_);
                    return v___x_4916_;
                }
            } else {
                let mut v___x_4917_: usize = 0;
                let mut v___x_4918_: usize = 0;
                let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
                v___x_4917_ = 1usize;
                v___x_4918_ = lean_usize_of_nat(v___x_4904_);
                v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_4902_, v___x_4917_, v___x_4918_, v_a0_4907_);
                v___x_4920_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4920_, 0, v___x_4919_);
                return v___x_4920_;
            }
        }
    }
}
pub unsafe fn l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(
    mut v_as_4921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4922_: *mut LeanObject = core::ptr::null_mut();
    v_res_4922_ =
        l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_4921_);
    lean_dec_ref(v_as_4921_);
    return v_res_4922_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(
    mut v_a_4923_: *mut LeanObject,
    mut v_a_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4930_: u8 = 0;
    let mut v_snd_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4923_) == 0 {
                    v___x_4925_ = lean_array_to_list(v_a_4924_);
                    return v___x_4925_;
                } else {
                    v_head_4926_ = lean_ctor_get(v_a_4923_, 0);
                    v_tail_4927_ = lean_ctor_get(v_a_4923_, 1);
                    v_isSharedCheck_4944_ = (!lean_is_exclusive(v_a_4923_)) as u8;
                    if v_isSharedCheck_4944_ == 0 {
                        v___x_4929_ = v_a_4923_;
                        v_isShared_4930_ = v_isSharedCheck_4944_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4927_);
                        lean_inc(v_head_4926_);
                        lean_dec(v_a_4923_);
                        v___x_4929_ = lean_box(0);
                        v_isShared_4930_ = v_isSharedCheck_4944_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4931_ = lean_ctor_get(v_head_4926_, 1);
                v___x_4932_ = l_Lean_Elab_Info_pos_x3f(v_snd_4931_);
                if lean_obj_tag(v___x_4932_) == 0 {
                    lean_del_object(v___x_4929_);
                    lean_dec(v_head_4926_);
                    v_a_4923_ = v_tail_4927_;
                    state = 0;
                    continue;
                } else {
                    v_val_4934_ = lean_ctor_get(v___x_4932_, 0);
                    lean_inc(v_val_4934_);
                    lean_dec_ref_known(v___x_4932_, 1);
                    v___x_4935_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_4931_);
                    if lean_obj_tag(v___x_4935_) == 0 {
                        lean_dec(v_val_4934_);
                        lean_del_object(v___x_4929_);
                        lean_dec(v_head_4926_);
                        v_a_4923_ = v_tail_4927_;
                        state = 0;
                        continue;
                    } else {
                        v_val_4937_ = lean_ctor_get(v___x_4935_, 0);
                        lean_inc(v_val_4937_);
                        lean_dec_ref_known(v___x_4935_, 1);
                        v___x_4938_ = lean_nat_sub(v_val_4937_, v_val_4934_);
                        lean_dec(v_val_4934_);
                        lean_dec(v_val_4937_);
                        if v_isShared_4930_ == 0 {
                            lean_ctor_set_tag(v___x_4929_, 0);
                            lean_ctor_set(v___x_4929_, 1, v_head_4926_);
                            lean_ctor_set(v___x_4929_, 0, v___x_4938_);
                            v___x_4940_ = v___x_4929_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4938_);
                            lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_head_4926_);
                            v___x_4940_ = v_reuseFailAlloc_4943_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4941_ = lean_array_push(v_a_4924_, v___x_4940_);
                v_a_4923_ = v_tail_4927_;
                v_a_4924_ = v___x_4941_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_smallestInfo_x3f(
    mut v_p_4947_: *mut LeanObject,
    mut v_t_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ts_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infos_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v_snd_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4949_ = lean_alloc_closure(
                    l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_4949_, 0, v_p_4947_);
                v_ts_4950_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_4949_, v_t_4948_);
                v___x_4951_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0;
                v_infos_4952_ =
                    l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(
                        v_ts_4950_,
                        v___x_4951_,
                    );
                v___x_4953_ = lean_array_mk(v_infos_4952_);
                v___x_4954_ =
                    l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(
                        v___x_4953_,
                    );
                lean_dec_ref(v___x_4953_);
                if lean_obj_tag(v___x_4954_) == 0 {
                    v___x_4955_ = lean_box(0);
                    return v___x_4955_;
                } else {
                    v_val_4956_ = lean_ctor_get(v___x_4954_, 0);
                    v_isSharedCheck_4964_ = (!lean_is_exclusive(v___x_4954_)) as u8;
                    if v_isSharedCheck_4964_ == 0 {
                        v___x_4958_ = v___x_4954_;
                        v_isShared_4959_ = v_isSharedCheck_4964_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4956_);
                        lean_dec(v___x_4954_);
                        v___x_4958_ = lean_box(0);
                        v_isShared_4959_ = v_isSharedCheck_4964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4960_ = lean_ctor_get(v_val_4956_, 1);
                lean_inc(v_snd_4960_);
                lean_dec(v_val_4956_);
                if v_isShared_4959_ == 0 {
                    lean_ctor_set(v___x_4958_, 0, v_snd_4960_);
                    v___x_4962_ = v___x_4958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_snd_4960_);
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instBEqHoverableInfoPrio_beq(
    mut v_x_4965_: *mut LeanObject,
    mut v_x_4966_: *mut LeanObject,
) -> u8 {
    let mut v_isHoverPosOnStop_4967_: u8 = 0;
    let mut v_size_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isVariableInfo_4969_: u8 = 0;
    let mut v_isPartialTermInfo_4970_: u8 = 0;
    let mut v_isHoverPosOnStop_4971_: u8 = 0;
    let mut v_size_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isVariableInfo_4973_: u8 = 0;
    let mut v_isPartialTermInfo_4974_: u8 = 0;
    let mut v___y_4976_: u8 = 0;
    let mut v___x_4978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isHoverPosOnStop_4967_ = lean_ctor_get_uint8(
                    v_x_4965_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_size_4968_ = lean_ctor_get(v_x_4965_, 0);
                v_isVariableInfo_4969_ = lean_ctor_get_uint8(
                    v_x_4965_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isPartialTermInfo_4970_ = lean_ctor_get_uint8(
                    v_x_4965_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_isHoverPosOnStop_4971_ = lean_ctor_get_uint8(
                    v_x_4966_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_size_4972_ = lean_ctor_get(v_x_4966_, 0);
                v_isVariableInfo_4973_ = lean_ctor_get_uint8(
                    v_x_4966_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isPartialTermInfo_4974_ = lean_ctor_get_uint8(
                    v_x_4966_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                if v_isHoverPosOnStop_4967_ == 0 {
                    if v_isHoverPosOnStop_4971_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        return v_isHoverPosOnStop_4967_;
                    }
                } else {
                    if v_isHoverPosOnStop_4971_ == 0 {
                        return v_isHoverPosOnStop_4971_;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4976_ == 0 {
                    return v___y_4976_;
                } else {
                    if v_isPartialTermInfo_4970_ == 0 {
                        if v_isPartialTermInfo_4974_ == 0 {
                            return v___y_4976_;
                        } else {
                            return v_isPartialTermInfo_4970_;
                        }
                    } else {
                        return v_isPartialTermInfo_4974_;
                    }
                }
            }
            2 => {
                v___x_4978_ = lean_nat_dec_eq(v_size_4968_, v_size_4972_);
                if v___x_4978_ == 0 {
                    return v___x_4978_;
                } else {
                    if v_isVariableInfo_4969_ == 0 {
                        if v_isVariableInfo_4973_ == 0 {
                            v___y_4976_ = v___x_4978_;
                            state = 1;
                            continue;
                        } else {
                            return v_isVariableInfo_4969_;
                        }
                    } else {
                        v___y_4976_ = v_isVariableInfo_4973_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(
    mut v_x_4979_: *mut LeanObject,
    mut v_x_4980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4981_: u8 = 0;
    let mut v_r_4982_: *mut LeanObject = core::ptr::null_mut();
    v_res_4981_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_4979_, v_x_4980_);
    lean_dec_ref(v_x_4980_);
    lean_dec_ref(v_x_4979_);
    v_r_4982_ = lean_box((v_res_4981_) as usize);
    return v_r_4982_;
}
pub unsafe fn l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(
    mut v_i1_4985_: *mut LeanObject,
    mut v_i2_4986_: *mut LeanObject,
) -> u8 {
    let mut v_isHoverPosOnStop_4987_: u8 = 0;
    let mut v_size_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isVariableInfo_4989_: u8 = 0;
    let mut v_isPartialTermInfo_4990_: u8 = 0;
    let mut v_isPartialTermInfo_4992_: u8 = 0;
    let mut v___x_4993_: u8 = 0;
    let mut v___x_4994_: u8 = 0;
    let mut v_isPartialTermInfo_4995_: u8 = 0;
    let mut v___x_4996_: u8 = 0;
    let mut v___x_4997_: u8 = 0;
    let mut v_isVariableInfo_4999_: u8 = 0;
    let mut v___x_5000_: u8 = 0;
    let mut v___y_5002_: u8 = 0;
    let mut v_size_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isVariableInfo_5004_: u8 = 0;
    let mut v___x_5005_: u8 = 0;
    let mut v___x_5006_: u8 = 0;
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: u8 = 0;
    let mut v___x_5009_: u8 = 0;
    let mut v_isHoverPosOnStop_5011_: u8 = 0;
    let mut v___x_5012_: u8 = 0;
    let mut v___y_5014_: u8 = 0;
    let mut v_isHoverPosOnStop_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isHoverPosOnStop_4987_ = lean_ctor_get_uint8(
                    v_i1_4985_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_size_4988_ = lean_ctor_get(v_i1_4985_, 0);
                v_isVariableInfo_4989_ = lean_ctor_get_uint8(
                    v_i1_4985_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isPartialTermInfo_4990_ = lean_ctor_get_uint8(
                    v_i1_4985_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                if v_isHoverPosOnStop_4987_ == 0 {
                    v___y_5014_ = v_isHoverPosOnStop_4987_;
                    state = 5;
                    continue;
                } else {
                    v_isHoverPosOnStop_5015_ = lean_ctor_get_uint8(
                        v_i2_4986_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_isHoverPosOnStop_5015_ == 0 {
                        v___x_5016_ = 0;
                        return v___x_5016_;
                    } else {
                        v___x_5017_ = 0;
                        v___y_5014_ = v___x_5017_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isPartialTermInfo_4990_ == 0 {
                    v_isPartialTermInfo_4992_ = lean_ctor_get_uint8(
                        v_i2_4986_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    );
                    if v_isPartialTermInfo_4992_ == 0 {
                        v___x_4993_ = 1;
                        return v___x_4993_;
                    } else {
                        v___x_4994_ = 2;
                        return v___x_4994_;
                    }
                } else {
                    v_isPartialTermInfo_4995_ = lean_ctor_get_uint8(
                        v_i2_4986_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    );
                    if v_isPartialTermInfo_4995_ == 0 {
                        v___x_4996_ = 0;
                        return v___x_4996_;
                    } else {
                        v___x_4997_ = 1;
                        return v___x_4997_;
                    }
                }
            }
            2 => {
                v_isVariableInfo_4999_ = lean_ctor_get_uint8(
                    v_i2_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                if v_isVariableInfo_4999_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_5000_ = 2;
                    return v___x_5000_;
                }
            }
            3 => {
                v_size_5003_ = lean_ctor_get(v_i2_4986_, 0);
                v_isVariableInfo_5004_ = lean_ctor_get_uint8(
                    v_i2_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v___x_5005_ = lean_nat_dec_lt(v_size_5003_, v_size_4988_);
                if v___x_5005_ == 0 {
                    v___x_5006_ = lean_nat_dec_lt(v_size_4988_, v_size_5003_);
                    if v___x_5006_ == 0 {
                        if v_isVariableInfo_4989_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            if v_isVariableInfo_5004_ == 0 {
                                v___x_5007_ = 0;
                                return v___x_5007_;
                            } else {
                                if v___y_5002_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5008_ = 2;
                        return v___x_5008_;
                    }
                } else {
                    v___x_5009_ = 0;
                    return v___x_5009_;
                }
            }
            4 => {
                v_isHoverPosOnStop_5011_ = lean_ctor_get_uint8(
                    v_i2_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_isHoverPosOnStop_5011_ == 0 {
                    v___y_5002_ = v_isHoverPosOnStop_5011_;
                    state = 3;
                    continue;
                } else {
                    v___x_5012_ = 2;
                    return v___x_5012_;
                }
            }
            5 => {
                if v_isHoverPosOnStop_4987_ == 0 {
                    state = 4;
                    continue;
                } else {
                    if v___y_5014_ == 0 {
                        v___y_5002_ = v___y_5014_;
                        state = 3;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(
    mut v_i1_5018_: *mut LeanObject,
    mut v_i2_5019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5020_: u8 = 0;
    let mut v_r_5021_: *mut LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_5018_, v_i2_5019_);
    lean_dec_ref(v_i2_5019_);
    lean_dec_ref(v_i1_5018_);
    v_r_5021_ = lean_box((v_res_5020_) as usize);
    return v_r_5021_;
}
pub unsafe fn _init_l_Lean_Elab_instLEHoverableInfoPrio() -> *mut LeanObject {
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    v___x_5024_ = lean_box(0);
    return v___x_5024_;
}
pub unsafe fn l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(
    mut v_x_5025_: *mut LeanObject,
    mut v_y_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5027_: u8 = 0;
    v___x_5027_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_5025_, v_y_5026_);
    if v___x_5027_ == 2 {
        lean_inc_ref(v_x_5025_);
        return v_x_5025_;
    } else {
        lean_inc_ref(v_y_5026_);
        return v_y_5026_;
    }
}
pub unsafe fn l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(
    mut v_x_5028_: *mut LeanObject,
    mut v_y_5029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5030_: *mut LeanObject = core::ptr::null_mut();
    v_res_5030_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_5028_, v_y_5029_);
    lean_dec_ref(v_y_5029_);
    lean_dec_ref(v_x_5028_);
    return v_res_5030_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(
    mut v_x_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5034_: *mut LeanObject = core::ptr::null_mut();
    v_fst_5034_ = lean_ctor_get(v_x_5033_, 0);
    lean_inc(v_fst_5034_);
    return v_fst_5034_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(
    mut v_x_5035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5036_: *mut LeanObject = core::ptr::null_mut();
    v_res_5036_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_5035_);
    lean_dec_ref(v_x_5035_);
    return v_res_5036_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(
    mut v_r_x3f_5037_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_x3f_5037_) == 0 {
        let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
        v___x_5038_ = lean_box(0);
        return v___x_5038_;
    } else {
        let mut v_val_5039_: *mut LeanObject = core::ptr::null_mut();
        v_val_5039_ = lean_ctor_get(v_r_x3f_5037_, 0);
        lean_inc(v_val_5039_);
        return v_val_5039_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(
    mut v_r_x3f_5040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5041_: *mut LeanObject = core::ptr::null_mut();
    v_res_5041_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_5040_);
    lean_dec(v_r_x3f_5040_);
    return v_res_5041_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(
    mut v___x_5042_: *mut LeanObject,
    mut v_maxPrio_x3f_5043_: *mut LeanObject,
    mut v_x_5044_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: u8 = 0;
    v_fst_5045_ = lean_ctor_get(v_x_5044_, 0);
    lean_inc(v_fst_5045_);
    v___x_5046_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5046_, 0, v_fst_5045_);
    v___x_5047_ = l_Option_instBEq_beq___redArg(v___x_5042_, v___x_5046_, v_maxPrio_x3f_5043_);
    return v___x_5047_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(
    mut v___x_5048_: *mut LeanObject,
    mut v_maxPrio_x3f_5049_: *mut LeanObject,
    mut v_x_5050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5051_: u8 = 0;
    let mut v_r_5052_: *mut LeanObject = core::ptr::null_mut();
    v_res_5051_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(
        v___x_5048_,
        v_maxPrio_x3f_5049_,
        v_x_5050_,
    );
    lean_dec_ref(v_x_5050_);
    v_r_5052_ = lean_box((v_res_5051_) as usize);
    return v_r_5052_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(
    mut v___f_5065_: *mut LeanObject,
    mut v___f_5066_: *mut LeanObject,
    mut v___x_5067_: *mut LeanObject,
    mut v_toPure_5068_: *mut LeanObject,
    mut v_ctx_5069_: *mut LeanObject,
    mut v_info_5070_: *mut LeanObject,
    mut v_children_5071_: *mut LeanObject,
    mut v_hoverPos_5072_: *mut LeanObject,
    mut v_includeStop_5073_: u8,
    mut v_results_5074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5076_: u8 = 0;
    let mut v___y_5077_: u8 = 0;
    let mut v___y_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5079_: u8 = 0;
    let mut v_priority_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5086_: u8 = 0;
    let mut v___y_5087_: u8 = 0;
    let mut v___y_5088_: u8 = 0;
    let mut v___y_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5090_: u8 = 0;
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxPrio_x3f_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bestResult_x3f_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5102_: u8 = 0;
    let mut v___y_5103_: u8 = 0;
    let mut v___y_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v_start_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5117_: u8 = 0;
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elaborator_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5094_ = lean_box(0);
                lean_inc(v_results_5074_);
                v___x_5095_ = l_List_mapTR_loop___redArg(v___f_5065_, v_results_5074_, v___x_5094_);
                v_maxPrio_x3f_5096_ = l_List_max_x3f___redArg(v___f_5066_, v___x_5095_);
                v___f_5097_ = lean_alloc_closure(
                    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_5097_, 0, v___x_5067_);
                lean_closure_set(v___f_5097_, 1, v_maxPrio_x3f_5096_);
                v_bestResult_x3f_5098_ = l_List_find_x3f___redArg(v___f_5097_, v_results_5074_);
                if lean_obj_tag(v_bestResult_x3f_5098_) == 1 {
                    lean_dec_ref(v_children_5071_);
                    lean_dec_ref(v_info_5070_);
                    lean_dec_ref(v_ctx_5069_);
                    v___x_5099_ = lean_apply_2(v_toPure_5068_, lean_box(0), v_bestResult_x3f_5098_);
                    return v___x_5099_;
                } else {
                    lean_dec(v_bestResult_x3f_5098_);
                    v___x_5100_ = l_Lean_Elab_Info_stx(v_info_5070_);
                    v___x_5122_ =
                        l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1;
                    lean_inc(v___x_5100_);
                    v___x_5123_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5122_);
                    if v___x_5123_ == 0 {
                        lean_inc_ref(v_info_5070_);
                        v___x_5124_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_5070_);
                        if lean_obj_tag(v___x_5124_) == 0 {
                            v___y_5117_ = v___x_5123_;
                            state = 5;
                            continue;
                        } else {
                            v_val_5125_ = lean_ctor_get(v___x_5124_, 0);
                            lean_inc(v_val_5125_);
                            lean_dec_ref_known(v___x_5124_, 1);
                            v_elaborator_5126_ = lean_ctor_get(v_val_5125_, 0);
                            lean_inc(v_elaborator_5126_);
                            lean_dec(v_val_5125_);
                            v___x_5127_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6;
                            v___x_5128_ = lean_name_eq(v_elaborator_5126_, v___x_5127_);
                            lean_dec(v_elaborator_5126_);
                            v___y_5117_ = v___x_5128_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_5117_ = v___x_5123_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_priority_5080_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v_priority_5080_, 0, v___y_5078_);
                lean_ctor_set_uint8(
                    v_priority_5080_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_5076_,
                );
                lean_ctor_set_uint8(
                    v_priority_5080_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___y_5077_,
                );
                lean_ctor_set_uint8(
                    v_priority_5080_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___y_5079_,
                );
                v_result_5081_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v_result_5081_, 0, v_ctx_5069_);
                lean_ctor_set(v_result_5081_, 1, v_info_5070_);
                lean_ctor_set(v_result_5081_, 2, v_children_5071_);
                v___x_5082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5082_, 0, v_priority_5080_);
                lean_ctor_set(v___x_5082_, 1, v_result_5081_);
                v___x_5083_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5083_, 0, v___x_5082_);
                v___x_5084_ = lean_apply_2(v_toPure_5068_, lean_box(0), v___x_5083_);
                return v___x_5084_;
            }
            2 => {
                if lean_obj_tag(v_info_5070_) == 2 {
                    v___y_5076_ = v___y_5086_;
                    v___y_5077_ = v___y_5090_;
                    v___y_5078_ = v___y_5089_;
                    v___y_5079_ = v___y_5088_;
                    state = 1;
                    continue;
                } else {
                    v___y_5076_ = v___y_5086_;
                    v___y_5077_ = v___y_5090_;
                    v___y_5078_ = v___y_5089_;
                    v___y_5079_ = v___y_5087_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5092_ = lean_box(0);
                v___x_5093_ = lean_apply_2(v_toPure_5068_, lean_box(0), v___x_5092_);
                return v___x_5093_;
            }
            4 => {
                v___x_5105_ = l_Lean_Syntax_getRange_x3f(v___x_5100_, v___y_5103_);
                lean_dec(v___x_5100_);
                if lean_obj_tag(v___x_5105_) == 1 {
                    v_val_5106_ = lean_ctor_get(v___x_5105_, 0);
                    lean_inc(v_val_5106_);
                    lean_dec_ref_known(v___x_5105_, 1);
                    v___x_5107_ = l_Lean_Syntax_Range_contains(
                        v_val_5106_,
                        v_hoverPos_5072_,
                        v_includeStop_5073_,
                    );
                    if v___x_5107_ == 0 {
                        lean_dec(v_val_5106_);
                        lean_dec_ref(v_children_5071_);
                        lean_dec_ref(v_info_5070_);
                        lean_dec_ref(v_ctx_5069_);
                        state = 3;
                        continue;
                    } else {
                        if v___y_5104_ == 0 {
                            lean_dec(v_val_5106_);
                            lean_dec_ref(v_children_5071_);
                            lean_dec_ref(v_info_5070_);
                            lean_dec_ref(v_ctx_5069_);
                            state = 3;
                            continue;
                        } else {
                            v_start_5108_ = lean_ctor_get(v_val_5106_, 0);
                            lean_inc(v_start_5108_);
                            v_stop_5109_ = lean_ctor_get(v_val_5106_, 1);
                            lean_inc(v_stop_5109_);
                            lean_dec(v_val_5106_);
                            v___x_5110_ = lean_nat_dec_eq(v_stop_5109_, v_hoverPos_5072_);
                            v___x_5111_ = lean_nat_sub(v_stop_5109_, v_start_5108_);
                            lean_dec(v_start_5108_);
                            lean_dec(v_stop_5109_);
                            if lean_obj_tag(v_info_5070_) == 1 {
                                v_i_5112_ = lean_ctor_get(v_info_5070_, 0);
                                v_expr_5113_ = lean_ctor_get(v_i_5112_, 3);
                                if lean_obj_tag(v_expr_5113_) == 1 {
                                    v___y_5086_ = v___x_5110_;
                                    v___y_5087_ = v___y_5102_;
                                    v___y_5088_ = v___y_5103_;
                                    v___y_5089_ = v___x_5111_;
                                    v___y_5090_ = v___y_5103_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___y_5086_ = v___x_5110_;
                                    v___y_5087_ = v___y_5102_;
                                    v___y_5088_ = v___y_5103_;
                                    v___y_5089_ = v___x_5111_;
                                    v___y_5090_ = v___y_5102_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_5086_ = v___x_5110_;
                                v___y_5087_ = v___y_5102_;
                                v___y_5088_ = v___y_5103_;
                                v___y_5089_ = v___x_5111_;
                                v___y_5090_ = v___y_5102_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_5105_);
                    lean_dec_ref(v_children_5071_);
                    lean_dec_ref(v_info_5070_);
                    lean_dec_ref(v_ctx_5069_);
                    v___x_5114_ = lean_box(0);
                    v___x_5115_ = lean_apply_2(v_toPure_5068_, lean_box(0), v___x_5114_);
                    return v___x_5115_;
                }
            }
            5 => {
                if v___y_5117_ == 0 {
                    v___x_5118_ = 1;
                    match lean_obj_tag(v_info_5070_) {
                        7 => {
                            v___y_5102_ = v___y_5117_;
                            v___y_5103_ = v___x_5118_;
                            v___y_5104_ = v___x_5118_;
                            state = 4;
                            continue;
                        }
                        5 => {
                            v___y_5102_ = v___y_5117_;
                            v___y_5103_ = v___x_5118_;
                            v___y_5104_ = v___x_5118_;
                            state = 4;
                            continue;
                        }
                        6 => {
                            v___y_5102_ = v___y_5117_;
                            v___y_5103_ = v___x_5118_;
                            v___y_5104_ = v___x_5118_;
                            state = 4;
                            continue;
                        }
                        _ => {
                            lean_inc_ref(v_info_5070_);
                            v___x_5119_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_5070_);
                            if lean_obj_tag(v___x_5119_) == 0 {
                                v___y_5102_ = v___y_5117_;
                                v___y_5103_ = v___x_5118_;
                                v___y_5104_ = v___y_5117_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_5119_, 1);
                                v___y_5102_ = v___y_5117_;
                                v___y_5103_ = v___x_5118_;
                                v___y_5104_ = v___x_5118_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_5100_);
                    lean_dec_ref(v_children_5071_);
                    lean_dec_ref(v_info_5070_);
                    lean_dec_ref(v_ctx_5069_);
                    v___x_5120_ = lean_box(0);
                    v___x_5121_ = lean_apply_2(v_toPure_5068_, lean_box(0), v___x_5120_);
                    return v___x_5121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(
    mut v___f_5129_: *mut LeanObject,
    mut v___f_5130_: *mut LeanObject,
    mut v___x_5131_: *mut LeanObject,
    mut v_toPure_5132_: *mut LeanObject,
    mut v_ctx_5133_: *mut LeanObject,
    mut v_info_5134_: *mut LeanObject,
    mut v_children_5135_: *mut LeanObject,
    mut v_hoverPos_5136_: *mut LeanObject,
    mut v_includeStop_5137_: *mut LeanObject,
    mut v_results_5138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_5139_: u8 = 0;
    let mut v_res_5140_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5139_ = (lean_unbox(v_includeStop_5137_) as u8);
    v_res_5140_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(
        v___f_5129_,
        v___f_5130_,
        v___x_5131_,
        v_toPure_5132_,
        v_ctx_5133_,
        v_info_5134_,
        v_children_5135_,
        v_hoverPos_5136_,
        v_includeStop_boxed_5139_,
        v_results_5138_,
    );
    lean_dec(v_hoverPos_5136_);
    return v_res_5140_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(
    mut v___f_5143_: *mut LeanObject,
    mut v___f_5144_: *mut LeanObject,
    mut v___x_5145_: *mut LeanObject,
    mut v_toPure_5146_: *mut LeanObject,
    mut v_hoverPos_5147_: *mut LeanObject,
    mut v_includeStop_5148_: u8,
    mut v___f_5149_: *mut LeanObject,
    mut v_filter_5150_: *mut LeanObject,
    mut v_toBind_5151_: *mut LeanObject,
    mut v_ctx_5152_: *mut LeanObject,
    mut v_info_5153_: *mut LeanObject,
    mut v_children_5154_: *mut LeanObject,
    mut v_results_5155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    v___x_5156_ = lean_box((v_includeStop_5148_) as usize);
    lean_inc_ref(v_children_5154_);
    lean_inc_ref(v_info_5153_);
    lean_inc_ref(v_ctx_5152_);
    v___f_5157_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_5157_, 0, v___f_5143_);
    lean_closure_set(v___f_5157_, 1, v___f_5144_);
    lean_closure_set(v___f_5157_, 2, v___x_5145_);
    lean_closure_set(v___f_5157_, 3, v_toPure_5146_);
    lean_closure_set(v___f_5157_, 4, v_ctx_5152_);
    lean_closure_set(v___f_5157_, 5, v_info_5153_);
    lean_closure_set(v___f_5157_, 6, v_children_5154_);
    lean_closure_set(v___f_5157_, 7, v_hoverPos_5147_);
    lean_closure_set(v___f_5157_, 8, v___x_5156_);
    v___x_5158_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0;
    v___x_5159_ = l_List_filterMapTR_go___redArg(v___f_5149_, v_results_5155_, v___x_5158_);
    v___x_5160_ = lean_apply_4(
        v_filter_5150_,
        v_ctx_5152_,
        v_info_5153_,
        v_children_5154_,
        v___x_5159_,
    );
    v___x_5161_ = lean_apply_4(
        v_toBind_5151_,
        lean_box(0),
        lean_box(0),
        v___x_5160_,
        v___f_5157_,
    );
    return v___x_5161_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(
    mut v___f_5162_: *mut LeanObject,
    mut v___f_5163_: *mut LeanObject,
    mut v___x_5164_: *mut LeanObject,
    mut v_toPure_5165_: *mut LeanObject,
    mut v_hoverPos_5166_: *mut LeanObject,
    mut v_includeStop_5167_: *mut LeanObject,
    mut v___f_5168_: *mut LeanObject,
    mut v_filter_5169_: *mut LeanObject,
    mut v_toBind_5170_: *mut LeanObject,
    mut v_ctx_5171_: *mut LeanObject,
    mut v_info_5172_: *mut LeanObject,
    mut v_children_5173_: *mut LeanObject,
    mut v_results_5174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_5175_: u8 = 0;
    let mut v_res_5176_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5175_ = (lean_unbox(v_includeStop_5167_) as u8);
    v_res_5176_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(
        v___f_5162_,
        v___f_5163_,
        v___x_5164_,
        v_toPure_5165_,
        v_hoverPos_5166_,
        v_includeStop_boxed_5175_,
        v___f_5168_,
        v_filter_5169_,
        v_toBind_5170_,
        v_ctx_5171_,
        v_info_5172_,
        v_children_5173_,
        v_results_5174_,
    );
    return v_res_5176_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(
    mut v_toPure_5177_: *mut LeanObject,
    mut v_results_5178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5186_: u8 = 0;
    let mut v_snd_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: u8 = 0;
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_results_5178_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_5182_ = lean_ctor_get(v_results_5178_, 0);
                    lean_inc(v_val_5182_);
                    lean_dec_ref_known(v_results_5178_, 1);
                    if lean_obj_tag(v_val_5182_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_5183_ = lean_ctor_get(v_val_5182_, 0);
                        v_isSharedCheck_5199_ = (!lean_is_exclusive(v_val_5182_)) as u8;
                        if v_isSharedCheck_5199_ == 0 {
                            v___x_5185_ = v_val_5182_;
                            v_isShared_5186_ = v_isSharedCheck_5199_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_5183_);
                            lean_dec(v_val_5182_);
                            v___x_5185_ = lean_box(0);
                            v_isShared_5186_ = v_isSharedCheck_5199_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5180_ = lean_box(0);
                v___x_5181_ = lean_apply_2(v_toPure_5177_, lean_box(0), v___x_5180_);
                return v___x_5181_;
            }
            2 => {
                v_snd_5187_ = lean_ctor_get(v_val_5183_, 1);
                lean_inc(v_snd_5187_);
                lean_dec(v_val_5183_);
                v_info_5188_ = lean_ctor_get(v_snd_5187_, 1);
                lean_inc_ref(v_info_5188_);
                if v_isShared_5186_ == 0 {
                    lean_ctor_set(v___x_5185_, 0, v_snd_5187_);
                    v___x_5190_ = v___x_5185_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_snd_5187_);
                    v___x_5190_ = v_reuseFailAlloc_5198_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_info_5188_) == 1 {
                    v_i_5191_ = lean_ctor_get(v_info_5188_, 0);
                    lean_inc_ref(v_i_5191_);
                    lean_dec_ref_known(v_info_5188_, 1);
                    v_expr_5192_ = lean_ctor_get(v_i_5191_, 3);
                    lean_inc_ref(v_expr_5192_);
                    lean_dec_ref(v_i_5191_);
                    v___x_5193_ = l_Lean_Expr_isSyntheticSorry(v_expr_5192_);
                    lean_dec_ref(v_expr_5192_);
                    if v___x_5193_ == 0 {
                        v___x_5194_ = lean_apply_2(v_toPure_5177_, lean_box(0), v___x_5190_);
                        return v___x_5194_;
                    } else {
                        lean_dec_ref(v___x_5190_);
                        v___x_5195_ = lean_box(0);
                        v___x_5196_ = lean_apply_2(v_toPure_5177_, lean_box(0), v___x_5195_);
                        return v___x_5196_;
                    }
                } else {
                    lean_dec_ref(v_info_5188_);
                    v___x_5197_ = lean_apply_2(v_toPure_5177_, lean_box(0), v___x_5190_);
                    return v___x_5197_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(
    mut v_inst_5202_: *mut LeanObject,
    mut v_t_5203_: *mut LeanObject,
    mut v_hoverPos_5204_: *mut LeanObject,
    mut v_includeStop_5205_: u8,
    mut v_filter_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postNode_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5207_ = lean_ctor_get(v_inst_5202_, 0);
    v_toBind_5208_ = lean_ctor_get(v_inst_5202_, 1);
    lean_inc_n(v_toBind_5208_, 2);
    v_toPure_5209_ = lean_ctor_get(v_toApplicative_5207_, 1);
    v___f_5210_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0;
    v___f_5211_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1;
    v___f_5212_ = l_Lean_Elab_instMaxHoverableInfoPrio___closed__0;
    v___x_5213_ = l_Lean_Elab_instBEqHoverableInfoPrio___closed__0;
    v___x_5214_ = lean_box((v_includeStop_5205_) as usize);
    lean_inc_n(v_toPure_5209_, 3);
    v_postNode_5215_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        13,
        9,
    );
    lean_closure_set(v_postNode_5215_, 0, v___f_5210_);
    lean_closure_set(v_postNode_5215_, 1, v___f_5212_);
    lean_closure_set(v_postNode_5215_, 2, v___x_5213_);
    lean_closure_set(v_postNode_5215_, 3, v_toPure_5209_);
    lean_closure_set(v_postNode_5215_, 4, v_hoverPos_5204_);
    lean_closure_set(v_postNode_5215_, 5, v___x_5214_);
    lean_closure_set(v_postNode_5215_, 6, v___f_5211_);
    lean_closure_set(v_postNode_5215_, 7, v_filter_5206_);
    lean_closure_set(v_postNode_5215_, 8, v_toBind_5208_);
    v___f_5216_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5216_, 0, v_toPure_5209_);
    v___f_5217_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5217_, 0, v_toPure_5209_);
    v___x_5218_ = lean_box(0);
    v___x_5219_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(
        v_inst_5202_,
        v___f_5216_,
        v_postNode_5215_,
        v___x_5218_,
        v_t_5203_,
    );
    v___x_5220_ = lean_apply_4(
        v_toBind_5208_,
        lean_box(0),
        lean_box(0),
        v___x_5219_,
        v___f_5217_,
    );
    return v___x_5220_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(
    mut v_inst_5221_: *mut LeanObject,
    mut v_t_5222_: *mut LeanObject,
    mut v_hoverPos_5223_: *mut LeanObject,
    mut v_includeStop_5224_: *mut LeanObject,
    mut v_filter_5225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_5226_: u8 = 0;
    let mut v_res_5227_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5226_ = (lean_unbox(v_includeStop_5224_) as u8);
    v_res_5227_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(
        v_inst_5221_,
        v_t_5222_,
        v_hoverPos_5223_,
        v_includeStop_boxed_5226_,
        v_filter_5225_,
    );
    return v_res_5227_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(
    mut v_m_5228_: *mut LeanObject,
    mut v_inst_5229_: *mut LeanObject,
    mut v_t_5230_: *mut LeanObject,
    mut v_hoverPos_5231_: *mut LeanObject,
    mut v_includeStop_5232_: u8,
    mut v_filter_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    v___x_5234_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(
        v_inst_5229_,
        v_t_5230_,
        v_hoverPos_5231_,
        v_includeStop_5232_,
        v_filter_5233_,
    );
    return v___x_5234_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(
    mut v_m_5235_: *mut LeanObject,
    mut v_inst_5236_: *mut LeanObject,
    mut v_t_5237_: *mut LeanObject,
    mut v_hoverPos_5238_: *mut LeanObject,
    mut v_includeStop_5239_: *mut LeanObject,
    mut v_filter_5240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_5241_: u8 = 0;
    let mut v_res_5242_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5241_ = (lean_unbox(v_includeStop_5239_) as u8);
    v_res_5242_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(
        v_m_5235_,
        v_inst_5236_,
        v_t_5237_,
        v_hoverPos_5238_,
        v_includeStop_boxed_5241_,
        v_filter_5240_,
    );
    return v_res_5242_;
}
pub unsafe fn l_Lean_Elab_Info_type_x3f(
    mut v_i_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5252_: u8 = 0;
    let mut v_expr_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_i_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v_val_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_a_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5295_: u8 = 0;
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_i_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v_toTermInfo_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5311_: u8 = 0;
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v_a_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_isSharedCheck_5327_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_i_5243_) {
                1 => {
                    v_i_5249_ = lean_ctor_get(v_i_5243_, 0);
                    v_isSharedCheck_5274_ = (!lean_is_exclusive(v_i_5243_)) as u8;
                    if v_isSharedCheck_5274_ == 0 {
                        v___x_5251_ = v_i_5243_;
                        v_isShared_5252_ = v_isSharedCheck_5274_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_5249_);
                        lean_dec(v_i_5243_);
                        v___x_5251_ = lean_box(0);
                        v_isShared_5252_ = v_isSharedCheck_5274_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_i_5275_ = lean_ctor_get(v_i_5243_, 0);
                    v_isSharedCheck_5300_ = (!lean_is_exclusive(v_i_5243_)) as u8;
                    if v_isSharedCheck_5300_ == 0 {
                        v___x_5277_ = v_i_5243_;
                        v_isShared_5278_ = v_isSharedCheck_5300_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_i_5275_);
                        lean_dec(v_i_5243_);
                        v___x_5277_ = lean_box(0);
                        v_isShared_5278_ = v_isSharedCheck_5300_;
                        state = 7;
                        continue;
                    }
                }
                13 => {
                    v_i_5301_ = lean_ctor_get(v_i_5243_, 0);
                    v_isSharedCheck_5327_ = (!lean_is_exclusive(v_i_5243_)) as u8;
                    if v_isSharedCheck_5327_ == 0 {
                        v___x_5303_ = v_i_5243_;
                        v_isShared_5304_ = v_isSharedCheck_5327_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_i_5301_);
                        lean_dec(v_i_5243_);
                        v___x_5303_ = lean_box(0);
                        v_isShared_5304_ = v_isSharedCheck_5327_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_i_5243_);
                    v___x_5328_ = lean_box(0);
                    v___x_5329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5329_, 0, v___x_5328_);
                    return v___x_5329_;
                }
            },
            1 => {
                v_expr_5253_ = lean_ctor_get(v_i_5249_, 3);
                lean_inc_ref(v_expr_5253_);
                lean_dec_ref(v_i_5249_);
                lean_inc(v_a_5247_);
                lean_inc_ref(v_a_5246_);
                lean_inc(v_a_5245_);
                lean_inc_ref(v_a_5244_);
                v___x_5254_ =
                    lean_infer_type(v_expr_5253_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
                if lean_obj_tag(v___x_5254_) == 0 {
                    v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
                    v_isSharedCheck_5265_ = (!lean_is_exclusive(v___x_5254_)) as u8;
                    if v_isSharedCheck_5265_ == 0 {
                        v___x_5257_ = v___x_5254_;
                        v_isShared_5258_ = v_isSharedCheck_5265_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5255_);
                        lean_dec(v___x_5254_);
                        v___x_5257_ = lean_box(0);
                        v_isShared_5258_ = v_isSharedCheck_5265_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5251_);
                    v_a_5266_ = lean_ctor_get(v___x_5254_, 0);
                    v_isSharedCheck_5273_ = (!lean_is_exclusive(v___x_5254_)) as u8;
                    if v_isSharedCheck_5273_ == 0 {
                        v___x_5268_ = v___x_5254_;
                        v_isShared_5269_ = v_isSharedCheck_5273_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5266_);
                        lean_dec(v___x_5254_);
                        v___x_5268_ = lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5273_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5252_ == 0 {
                    lean_ctor_set(v___x_5251_, 0, v_a_5255_);
                    v___x_5260_ = v___x_5251_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5258_ == 0 {
                    lean_ctor_set(v___x_5257_, 0, v___x_5260_);
                    v___x_5262_ = v___x_5257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5262_;
            }
            5 => {
                if v_isShared_5269_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
                    v___x_5271_ = v_reuseFailAlloc_5272_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5271_;
            }
            7 => {
                v_val_5279_ = lean_ctor_get(v_i_5275_, 3);
                lean_inc_ref(v_val_5279_);
                lean_dec_ref(v_i_5275_);
                lean_inc(v_a_5247_);
                lean_inc_ref(v_a_5246_);
                lean_inc(v_a_5245_);
                lean_inc_ref(v_a_5244_);
                v___x_5280_ =
                    lean_infer_type(v_val_5279_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
                if lean_obj_tag(v___x_5280_) == 0 {
                    v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
                    v_isSharedCheck_5291_ = (!lean_is_exclusive(v___x_5280_)) as u8;
                    if v_isSharedCheck_5291_ == 0 {
                        v___x_5283_ = v___x_5280_;
                        v_isShared_5284_ = v_isSharedCheck_5291_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5281_);
                        lean_dec(v___x_5280_);
                        v___x_5283_ = lean_box(0);
                        v_isShared_5284_ = v_isSharedCheck_5291_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5277_);
                    v_a_5292_ = lean_ctor_get(v___x_5280_, 0);
                    v_isSharedCheck_5299_ = (!lean_is_exclusive(v___x_5280_)) as u8;
                    if v_isSharedCheck_5299_ == 0 {
                        v___x_5294_ = v___x_5280_;
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5292_);
                        lean_dec(v___x_5280_);
                        v___x_5294_ = lean_box(0);
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5278_ == 0 {
                    lean_ctor_set_tag(v___x_5277_, 1);
                    lean_ctor_set(v___x_5277_, 0, v_a_5281_);
                    v___x_5286_ = v___x_5277_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5281_);
                    v___x_5286_ = v_reuseFailAlloc_5290_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5284_ == 0 {
                    lean_ctor_set(v___x_5283_, 0, v___x_5286_);
                    v___x_5288_ = v___x_5283_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5286_);
                    v___x_5288_ = v_reuseFailAlloc_5289_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5288_;
            }
            11 => {
                if v_isShared_5295_ == 0 {
                    v___x_5297_ = v___x_5294_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
                    v___x_5297_ = v_reuseFailAlloc_5298_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5297_;
            }
            13 => {
                v_toTermInfo_5305_ = lean_ctor_get(v_i_5301_, 0);
                lean_inc_ref(v_toTermInfo_5305_);
                lean_dec_ref(v_i_5301_);
                v_expr_5306_ = lean_ctor_get(v_toTermInfo_5305_, 3);
                lean_inc_ref(v_expr_5306_);
                lean_dec_ref(v_toTermInfo_5305_);
                lean_inc(v_a_5247_);
                lean_inc_ref(v_a_5246_);
                lean_inc(v_a_5245_);
                lean_inc_ref(v_a_5244_);
                v___x_5307_ =
                    lean_infer_type(v_expr_5306_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
                if lean_obj_tag(v___x_5307_) == 0 {
                    v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
                    v_isSharedCheck_5318_ = (!lean_is_exclusive(v___x_5307_)) as u8;
                    if v_isSharedCheck_5318_ == 0 {
                        v___x_5310_ = v___x_5307_;
                        v_isShared_5311_ = v_isSharedCheck_5318_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5308_);
                        lean_dec(v___x_5307_);
                        v___x_5310_ = lean_box(0);
                        v_isShared_5311_ = v_isSharedCheck_5318_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5303_);
                    v_a_5319_ = lean_ctor_get(v___x_5307_, 0);
                    v_isSharedCheck_5326_ = (!lean_is_exclusive(v___x_5307_)) as u8;
                    if v_isSharedCheck_5326_ == 0 {
                        v___x_5321_ = v___x_5307_;
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5319_);
                        lean_dec(v___x_5307_);
                        v___x_5321_ = lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_5304_ == 0 {
                    lean_ctor_set_tag(v___x_5303_, 1);
                    lean_ctor_set(v___x_5303_, 0, v_a_5308_);
                    v___x_5313_ = v___x_5303_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5308_);
                    v___x_5313_ = v_reuseFailAlloc_5317_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_5311_ == 0 {
                    lean_ctor_set(v___x_5310_, 0, v___x_5313_);
                    v___x_5315_ = v___x_5310_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5315_;
            }
            17 => {
                if v_isShared_5322_ == 0 {
                    v___x_5324_ = v___x_5321_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_type_x3f___boxed(
    mut v_i_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5336_: *mut LeanObject = core::ptr::null_mut();
    v_res_5336_ = l_Lean_Elab_Info_type_x3f(v_i_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_);
    lean_dec(v_a_5334_);
    lean_dec_ref(v_a_5333_);
    lean_dec(v_a_5332_);
    lean_dec_ref(v_a_5331_);
    return v_res_5336_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(
    mut v_name_5337_: *mut LeanObject,
    mut v___y_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    v___x_5340_ = lean_st_ref_get(v___y_5338_);
    v_env_5341_ = lean_ctor_get(v___x_5340_, 0);
    lean_inc_ref(v_env_5341_);
    lean_dec(v___x_5340_);
    v___x_5342_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_5343_ = lean_ctor_get(v___x_5342_, 0);
    v_asyncMode_5344_ = lean_ctor_get(v_toEnvExtension_5343_, 2);
    v___x_5345_ = lean_box(1);
    v___x_5346_ = lean_box(0);
    v___x_5347_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_5345_,
        v___x_5342_,
        v_env_5341_,
        v_asyncMode_5344_,
        v___x_5346_,
    );
    v___x_5348_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_5347_,
            v_name_5337_,
        );
    lean_dec(v___x_5347_);
    v___x_5349_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5349_, 0, v___x_5348_);
    return v___x_5349_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(
    mut v_name_5350_: *mut LeanObject,
    mut v___y_5351_: *mut LeanObject,
    mut v___y_5352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5353_: *mut LeanObject = core::ptr::null_mut();
    v_res_5353_ =
        l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(
            v_name_5350_,
            v___y_5351_,
        );
    lean_dec(v___y_5351_);
    lean_dec(v_name_5350_);
    return v_res_5353_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(
    mut v_name_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    v___x_5360_ =
        l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(
            v_name_5354_,
            v___y_5358_,
        );
    return v___x_5360_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(
    mut v_name_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5367_: *mut LeanObject = core::ptr::null_mut();
    v_res_5367_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(
        v_name_5361_,
        v___y_5362_,
        v___y_5363_,
        v___y_5364_,
        v___y_5365_,
    );
    lean_dec(v___y_5365_);
    lean_dec_ref(v___y_5364_);
    lean_dec(v___y_5363_);
    lean_dec_ref(v___y_5362_);
    lean_dec(v_name_5361_);
    return v_res_5367_;
}
pub unsafe fn l_Lean_Elab_Info_docString_x3f(
    mut v_i_5368_: *mut LeanObject,
    mut v_a_5369_: *mut LeanObject,
    mut v_a_5370_: *mut LeanObject,
    mut v_a_5371_: *mut LeanObject,
    mut v_a_5372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v_elaborator_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: u8 = 0;
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_a_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v_ref_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v_a_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5428_: u8 = 0;
    let mut v_ref_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5441_: u8 = 0;
    let mut v_isSharedCheck_5442_: u8 = 0;
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5452_: u8 = 0;
    let mut v___x_5453_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5458_: u8 = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5462_: u8 = 0;
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v_ref_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_i_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTermInfo_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5502_: u8 = 0;
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_a_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v_ref_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_isSharedCheck_5523_: u8 = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v_a_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5530_: u8 = 0;
    let mut v_ref_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_unused_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut v_i_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5555_: u8 = 0;
    let mut v_projName_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v_a_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v_ref_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_i_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v_optionName_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5602_: u8 = 0;
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5607_: u8 = 0;
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5615_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut v_a_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_ref_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut v_a_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v_ref_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_i_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorName_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v_val_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut v_i_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5680_: u8 = 0;
    let mut v_stx_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5684_: u8 = 0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5695_: u8 = 0;
    let mut v_a_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v_ref_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v_isSharedCheck_5713_: u8 = 0;
    let mut v_unused_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5715_: u8 = 0;
    let mut v_i_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5719_: u8 = 0;
    let mut v_name_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5730_: u8 = 0;
    let mut v_a_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5734_: u8 = 0;
    let mut v_ref_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5745_: u8 = 0;
    let mut v_isSharedCheck_5746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5374_ = lean_st_ref_get(v_a_5372_);
                v_env_5375_ = lean_ctor_get(v___x_5374_, 0);
                lean_inc_ref(v_env_5375_);
                lean_dec(v___x_5374_);
                match lean_obj_tag(v_i_5368_) {
                    1 => {
                        v_i_5446_ = lean_ctor_get(v_i_5368_, 0);
                        v_expr_5447_ = lean_ctor_get(v_i_5446_, 3);
                        v___x_5448_ = l_Lean_Expr_constName_x3f(v_expr_5447_);
                        if lean_obj_tag(v___x_5448_) == 1 {
                            lean_dec_ref_known(v_i_5368_, 1);
                            v_val_5449_ = lean_ctor_get(v___x_5448_, 0);
                            v_isSharedCheck_5478_ = (!lean_is_exclusive(v___x_5448_)) as u8;
                            if v_isSharedCheck_5478_ == 0 {
                                v___x_5451_ = v___x_5448_;
                                v_isShared_5452_ = v_isSharedCheck_5478_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_val_5449_);
                                lean_dec(v___x_5448_);
                                v___x_5451_ = lean_box(0);
                                v_isShared_5452_ = v_isSharedCheck_5478_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_5448_);
                            v___y_5377_ = v_a_5371_;
                            state = 1;
                            continue;
                        }
                    }
                    13 => {
                        v_i_5479_ = lean_ctor_get(v_i_5368_, 0);
                        v___x_5480_ =
                            l_Lean_Meta_getPPContext(v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_);
                        if lean_obj_tag(v___x_5480_) == 0 {
                            v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
                            lean_inc(v_a_5481_);
                            lean_dec_ref_known(v___x_5480_, 1);
                            lean_inc_ref(v_i_5479_);
                            v___x_5482_ =
                                l_Lean_Elab_DelabTermInfo_docString_x3f(v_a_5481_, v_i_5479_);
                            if lean_obj_tag(v___x_5482_) == 0 {
                                v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
                                v_isSharedCheck_5523_ = (!lean_is_exclusive(v___x_5482_)) as u8;
                                if v_isSharedCheck_5523_ == 0 {
                                    v___x_5485_ = v___x_5482_;
                                    v_isShared_5486_ = v_isSharedCheck_5523_;
                                    state = 22;
                                    continue;
                                } else {
                                    lean_inc(v_a_5483_);
                                    lean_dec(v___x_5482_);
                                    v___x_5485_ = lean_box(0);
                                    v_isShared_5486_ = v_isSharedCheck_5523_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_env_5375_);
                                v_isSharedCheck_5542_ = (!lean_is_exclusive(v_i_5368_)) as u8;
                                if v_isSharedCheck_5542_ == 0 {
                                    v_unused_5543_ = lean_ctor_get(v_i_5368_, 0);
                                    lean_dec(v_unused_5543_);
                                    v___x_5525_ = v_i_5368_;
                                    v_isShared_5526_ = v_isSharedCheck_5542_;
                                    state = 30;
                                    continue;
                                } else {
                                    lean_dec(v_i_5368_);
                                    v___x_5525_ = lean_box(0);
                                    v_isShared_5526_ = v_isSharedCheck_5542_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_i_5368_, 1);
                            lean_dec_ref(v_env_5375_);
                            v_a_5544_ = lean_ctor_get(v___x_5480_, 0);
                            v_isSharedCheck_5551_ = (!lean_is_exclusive(v___x_5480_)) as u8;
                            if v_isSharedCheck_5551_ == 0 {
                                v___x_5546_ = v___x_5480_;
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_a_5544_);
                                lean_dec(v___x_5480_);
                                v___x_5546_ = lean_box(0);
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 34;
                                continue;
                            }
                        }
                    }
                    7 => {
                        v_i_5552_ = lean_ctor_get(v_i_5368_, 0);
                        v_isSharedCheck_5582_ = (!lean_is_exclusive(v_i_5368_)) as u8;
                        if v_isSharedCheck_5582_ == 0 {
                            v___x_5554_ = v_i_5368_;
                            v_isShared_5555_ = v_isSharedCheck_5582_;
                            state = 36;
                            continue;
                        } else {
                            lean_inc(v_i_5552_);
                            lean_dec(v_i_5368_);
                            v___x_5554_ = lean_box(0);
                            v_isShared_5555_ = v_isSharedCheck_5582_;
                            state = 36;
                            continue;
                        }
                    }
                    5 => {
                        v_i_5583_ = lean_ctor_get(v_i_5368_, 0);
                        v_isSharedCheck_5652_ = (!lean_is_exclusive(v_i_5368_)) as u8;
                        if v_isSharedCheck_5652_ == 0 {
                            v___x_5585_ = v_i_5368_;
                            v_isShared_5586_ = v_isSharedCheck_5652_;
                            state = 42;
                            continue;
                        } else {
                            lean_inc(v_i_5583_);
                            lean_dec(v_i_5368_);
                            v___x_5585_ = lean_box(0);
                            v_isShared_5586_ = v_isSharedCheck_5652_;
                            state = 42;
                            continue;
                        }
                    }
                    6 => {
                        lean_dec_ref(v_env_5375_);
                        v_i_5653_ = lean_ctor_get(v_i_5368_, 0);
                        lean_inc_ref(v_i_5653_);
                        lean_dec_ref_known(v_i_5368_, 1);
                        v_errorName_5654_ = lean_ctor_get(v_i_5653_, 1);
                        lean_inc(v_errorName_5654_);
                        lean_dec_ref(v_i_5653_);
                        v___x_5655_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_errorName_5654_, v_a_5372_);
                        lean_dec(v_errorName_5654_);
                        v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
                        v_isSharedCheck_5676_ = (!lean_is_exclusive(v___x_5655_)) as u8;
                        if v_isSharedCheck_5676_ == 0 {
                            v___x_5658_ = v___x_5655_;
                            v_isShared_5659_ = v_isSharedCheck_5676_;
                            state = 56;
                            continue;
                        } else {
                            lean_inc(v_a_5656_);
                            lean_dec(v___x_5655_);
                            v___x_5658_ = lean_box(0);
                            v_isShared_5659_ = v_isSharedCheck_5676_;
                            state = 56;
                            continue;
                        }
                    }
                    15 => {
                        v_i_5677_ = lean_ctor_get(v_i_5368_, 0);
                        v_isSharedCheck_5715_ = (!lean_is_exclusive(v_i_5368_)) as u8;
                        if v_isSharedCheck_5715_ == 0 {
                            v___x_5679_ = v_i_5368_;
                            v_isShared_5680_ = v_isSharedCheck_5715_;
                            state = 61;
                            continue;
                        } else {
                            lean_inc(v_i_5677_);
                            lean_dec(v_i_5368_);
                            v___x_5679_ = lean_box(0);
                            v_isShared_5680_ = v_isSharedCheck_5715_;
                            state = 61;
                            continue;
                        }
                    }
                    16 => {
                        v_i_5716_ = lean_ctor_get(v_i_5368_, 0);
                        v_isSharedCheck_5746_ = (!lean_is_exclusive(v_i_5368_)) as u8;
                        if v_isSharedCheck_5746_ == 0 {
                            v___x_5718_ = v_i_5368_;
                            v_isShared_5719_ = v_isSharedCheck_5746_;
                            state = 69;
                            continue;
                        } else {
                            lean_inc(v_i_5716_);
                            lean_dec(v_i_5368_);
                            v___x_5718_ = lean_box(0);
                            v_isShared_5719_ = v_isSharedCheck_5746_;
                            state = 69;
                            continue;
                        }
                    }
                    _ => {
                        v___y_5377_ = v_a_5371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5378_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_5368_);
                if lean_obj_tag(v___x_5378_) == 1 {
                    v_val_5379_ = lean_ctor_get(v___x_5378_, 0);
                    v_isSharedCheck_5443_ = (!lean_is_exclusive(v___x_5378_)) as u8;
                    if v_isSharedCheck_5443_ == 0 {
                        v___x_5381_ = v___x_5378_;
                        v_isShared_5382_ = v_isSharedCheck_5443_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_5379_);
                        lean_dec(v___x_5378_);
                        v___x_5381_ = lean_box(0);
                        v_isShared_5382_ = v_isSharedCheck_5443_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5378_);
                    lean_dec_ref(v_env_5375_);
                    v___x_5444_ = lean_box(0);
                    v___x_5445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5445_, 0, v___x_5444_);
                    return v___x_5445_;
                }
            }
            2 => {
                v_elaborator_5383_ = lean_ctor_get(v_val_5379_, 0);
                v_stx_5384_ = lean_ctor_get(v_val_5379_, 1);
                v_isSharedCheck_5442_ = (!lean_is_exclusive(v_val_5379_)) as u8;
                if v_isSharedCheck_5442_ == 0 {
                    v___x_5386_ = v_val_5379_;
                    v_isShared_5387_ = v_isSharedCheck_5442_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_stx_5384_);
                    lean_inc(v_elaborator_5383_);
                    lean_dec(v_val_5379_);
                    v___x_5386_ = lean_box(0);
                    v_isShared_5387_ = v_isSharedCheck_5442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5388_ = l_Lean_Syntax_getKind(v_stx_5384_);
                v___x_5389_ = 1;
                lean_inc_ref(v_env_5375_);
                v___x_5390_ = l_Lean_findDocString_x3f(v_env_5375_, v___x_5388_, v___x_5389_);
                if lean_obj_tag(v___x_5390_) == 0 {
                    v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
                    v_isSharedCheck_5424_ = (!lean_is_exclusive(v___x_5390_)) as u8;
                    if v_isSharedCheck_5424_ == 0 {
                        v___x_5393_ = v___x_5390_;
                        v_isShared_5394_ = v_isSharedCheck_5424_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5391_);
                        lean_dec(v___x_5390_);
                        v___x_5393_ = lean_box(0);
                        v_isShared_5394_ = v_isSharedCheck_5424_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_elaborator_5383_);
                    lean_dec_ref(v_env_5375_);
                    v_a_5425_ = lean_ctor_get(v___x_5390_, 0);
                    v_isSharedCheck_5441_ = (!lean_is_exclusive(v___x_5390_)) as u8;
                    if v_isSharedCheck_5441_ == 0 {
                        v___x_5427_ = v___x_5390_;
                        v_isShared_5428_ = v_isSharedCheck_5441_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5425_);
                        lean_dec(v___x_5390_);
                        v___x_5427_ = lean_box(0);
                        v_isShared_5428_ = v_isSharedCheck_5441_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_5391_) == 0 {
                    lean_del_object(v___x_5393_);
                    v___x_5395_ =
                        l_Lean_findDocString_x3f(v_env_5375_, v_elaborator_5383_, v___x_5389_);
                    if lean_obj_tag(v___x_5395_) == 0 {
                        lean_del_object(v___x_5386_);
                        lean_del_object(v___x_5381_);
                        v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
                        v_isSharedCheck_5403_ = (!lean_is_exclusive(v___x_5395_)) as u8;
                        if v_isSharedCheck_5403_ == 0 {
                            v___x_5398_ = v___x_5395_;
                            v_isShared_5399_ = v_isSharedCheck_5403_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5396_);
                            lean_dec(v___x_5395_);
                            v___x_5398_ = lean_box(0);
                            v_isShared_5399_ = v_isSharedCheck_5403_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_5404_ = lean_ctor_get(v___x_5395_, 0);
                        v_isSharedCheck_5420_ = (!lean_is_exclusive(v___x_5395_)) as u8;
                        if v_isSharedCheck_5420_ == 0 {
                            v___x_5406_ = v___x_5395_;
                            v_isShared_5407_ = v_isSharedCheck_5420_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5404_);
                            lean_dec(v___x_5395_);
                            v___x_5406_ = lean_box(0);
                            v_isShared_5407_ = v_isSharedCheck_5420_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5386_);
                    lean_dec(v_elaborator_5383_);
                    lean_del_object(v___x_5381_);
                    lean_dec_ref(v_env_5375_);
                    if v_isShared_5394_ == 0 {
                        v___x_5422_ = v___x_5393_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5391_);
                        v___x_5422_ = v_reuseFailAlloc_5423_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5399_ == 0 {
                    v___x_5401_ = v___x_5398_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
                    v___x_5401_ = v_reuseFailAlloc_5402_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5401_;
            }
            7 => {
                v_ref_5408_ = lean_ctor_get(v___y_5377_, 5);
                v___x_5409_ = lean_io_error_to_string(v_a_5404_);
                if v_isShared_5382_ == 0 {
                    lean_ctor_set_tag(v___x_5381_, 3);
                    lean_ctor_set(v___x_5381_, 0, v___x_5409_);
                    v___x_5411_ = v___x_5381_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5409_);
                    v___x_5411_ = v_reuseFailAlloc_5419_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5412_ = l_Lean_MessageData_ofFormat(v___x_5411_);
                lean_inc(v_ref_5408_);
                if v_isShared_5387_ == 0 {
                    lean_ctor_set(v___x_5386_, 1, v___x_5412_);
                    lean_ctor_set(v___x_5386_, 0, v_ref_5408_);
                    v___x_5414_ = v___x_5386_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_ref_5408_);
                    lean_ctor_set(v_reuseFailAlloc_5418_, 1, v___x_5412_);
                    v___x_5414_ = v_reuseFailAlloc_5418_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5407_ == 0 {
                    lean_ctor_set(v___x_5406_, 0, v___x_5414_);
                    v___x_5416_ = v___x_5406_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5414_);
                    v___x_5416_ = v_reuseFailAlloc_5417_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5416_;
            }
            11 => {
                return v___x_5422_;
            }
            12 => {
                v_ref_5429_ = lean_ctor_get(v___y_5377_, 5);
                v___x_5430_ = lean_io_error_to_string(v_a_5425_);
                if v_isShared_5382_ == 0 {
                    lean_ctor_set_tag(v___x_5381_, 3);
                    lean_ctor_set(v___x_5381_, 0, v___x_5430_);
                    v___x_5432_ = v___x_5381_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5440_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5430_);
                    v___x_5432_ = v_reuseFailAlloc_5440_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5433_ = l_Lean_MessageData_ofFormat(v___x_5432_);
                lean_inc(v_ref_5429_);
                if v_isShared_5387_ == 0 {
                    lean_ctor_set(v___x_5386_, 1, v___x_5433_);
                    lean_ctor_set(v___x_5386_, 0, v_ref_5429_);
                    v___x_5435_ = v___x_5386_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_ref_5429_);
                    lean_ctor_set(v_reuseFailAlloc_5439_, 1, v___x_5433_);
                    v___x_5435_ = v_reuseFailAlloc_5439_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5428_ == 0 {
                    lean_ctor_set(v___x_5427_, 0, v___x_5435_);
                    v___x_5437_ = v___x_5427_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5435_);
                    v___x_5437_ = v_reuseFailAlloc_5438_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5437_;
            }
            16 => {
                v___x_5453_ = 1;
                v___x_5454_ = l_Lean_findDocString_x3f(v_env_5375_, v_val_5449_, v___x_5453_);
                if lean_obj_tag(v___x_5454_) == 0 {
                    lean_del_object(v___x_5451_);
                    v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
                    v_isSharedCheck_5462_ = (!lean_is_exclusive(v___x_5454_)) as u8;
                    if v_isSharedCheck_5462_ == 0 {
                        v___x_5457_ = v___x_5454_;
                        v_isShared_5458_ = v_isSharedCheck_5462_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5455_);
                        lean_dec(v___x_5454_);
                        v___x_5457_ = lean_box(0);
                        v_isShared_5458_ = v_isSharedCheck_5462_;
                        state = 17;
                        continue;
                    }
                } else {
                    v_a_5463_ = lean_ctor_get(v___x_5454_, 0);
                    v_isSharedCheck_5477_ = (!lean_is_exclusive(v___x_5454_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5465_ = v___x_5454_;
                        v_isShared_5466_ = v_isSharedCheck_5477_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_5463_);
                        lean_dec(v___x_5454_);
                        v___x_5465_ = lean_box(0);
                        v_isShared_5466_ = v_isSharedCheck_5477_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5458_ == 0 {
                    v___x_5460_ = v___x_5457_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
                    v___x_5460_ = v_reuseFailAlloc_5461_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5460_;
            }
            19 => {
                v_ref_5467_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5468_ = lean_io_error_to_string(v_a_5463_);
                if v_isShared_5452_ == 0 {
                    lean_ctor_set_tag(v___x_5451_, 3);
                    lean_ctor_set(v___x_5451_, 0, v___x_5468_);
                    v___x_5470_ = v___x_5451_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5476_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5468_);
                    v___x_5470_ = v_reuseFailAlloc_5476_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5471_ = l_Lean_MessageData_ofFormat(v___x_5470_);
                lean_inc(v_ref_5467_);
                v___x_5472_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5472_, 0, v_ref_5467_);
                lean_ctor_set(v___x_5472_, 1, v___x_5471_);
                if v_isShared_5466_ == 0 {
                    lean_ctor_set(v___x_5465_, 0, v___x_5472_);
                    v___x_5474_ = v___x_5465_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5472_);
                    v___x_5474_ = v_reuseFailAlloc_5475_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5474_;
            }
            22 => {
                if lean_obj_tag(v_a_5483_) == 1 {
                    lean_dec_ref_known(v_i_5368_, 1);
                    lean_dec_ref(v_env_5375_);
                    if v_isShared_5486_ == 0 {
                        v___x_5488_ = v___x_5485_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
                        v___x_5488_ = v_reuseFailAlloc_5489_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5485_);
                    lean_dec(v_a_5483_);
                    v_toTermInfo_5490_ = lean_ctor_get(v_i_5479_, 0);
                    v_expr_5491_ = lean_ctor_get(v_toTermInfo_5490_, 3);
                    v___x_5492_ = l_Lean_Expr_constName_x3f(v_expr_5491_);
                    if lean_obj_tag(v___x_5492_) == 1 {
                        lean_dec_ref_known(v_i_5368_, 1);
                        v_val_5493_ = lean_ctor_get(v___x_5492_, 0);
                        v_isSharedCheck_5522_ = (!lean_is_exclusive(v___x_5492_)) as u8;
                        if v_isSharedCheck_5522_ == 0 {
                            v___x_5495_ = v___x_5492_;
                            v_isShared_5496_ = v_isSharedCheck_5522_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_val_5493_);
                            lean_dec(v___x_5492_);
                            v___x_5495_ = lean_box(0);
                            v_isShared_5496_ = v_isSharedCheck_5522_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5492_);
                        v___y_5377_ = v_a_5371_;
                        state = 1;
                        continue;
                    }
                }
            }
            23 => {
                return v___x_5488_;
            }
            24 => {
                v___x_5497_ = 1;
                v___x_5498_ = l_Lean_findDocString_x3f(v_env_5375_, v_val_5493_, v___x_5497_);
                if lean_obj_tag(v___x_5498_) == 0 {
                    lean_del_object(v___x_5495_);
                    v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
                    v_isSharedCheck_5506_ = (!lean_is_exclusive(v___x_5498_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5501_ = v___x_5498_;
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_5499_);
                        lean_dec(v___x_5498_);
                        v___x_5501_ = lean_box(0);
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 25;
                        continue;
                    }
                } else {
                    v_a_5507_ = lean_ctor_get(v___x_5498_, 0);
                    v_isSharedCheck_5521_ = (!lean_is_exclusive(v___x_5498_)) as u8;
                    if v_isSharedCheck_5521_ == 0 {
                        v___x_5509_ = v___x_5498_;
                        v_isShared_5510_ = v_isSharedCheck_5521_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_5507_);
                        lean_dec(v___x_5498_);
                        v___x_5509_ = lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5521_;
                        state = 27;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_5502_ == 0 {
                    v___x_5504_ = v___x_5501_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
                    v___x_5504_ = v_reuseFailAlloc_5505_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5504_;
            }
            27 => {
                v_ref_5511_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5512_ = lean_io_error_to_string(v_a_5507_);
                if v_isShared_5496_ == 0 {
                    lean_ctor_set_tag(v___x_5495_, 3);
                    lean_ctor_set(v___x_5495_, 0, v___x_5512_);
                    v___x_5514_ = v___x_5495_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5512_);
                    v___x_5514_ = v_reuseFailAlloc_5520_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_5515_ = l_Lean_MessageData_ofFormat(v___x_5514_);
                lean_inc(v_ref_5511_);
                v___x_5516_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5516_, 0, v_ref_5511_);
                lean_ctor_set(v___x_5516_, 1, v___x_5515_);
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 0, v___x_5516_);
                    v___x_5518_ = v___x_5509_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5516_);
                    v___x_5518_ = v_reuseFailAlloc_5519_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5518_;
            }
            30 => {
                v_a_5527_ = lean_ctor_get(v___x_5482_, 0);
                v_isSharedCheck_5541_ = (!lean_is_exclusive(v___x_5482_)) as u8;
                if v_isSharedCheck_5541_ == 0 {
                    v___x_5529_ = v___x_5482_;
                    v_isShared_5530_ = v_isSharedCheck_5541_;
                    state = 31;
                    continue;
                } else {
                    lean_inc(v_a_5527_);
                    lean_dec(v___x_5482_);
                    v___x_5529_ = lean_box(0);
                    v_isShared_5530_ = v_isSharedCheck_5541_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v_ref_5531_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5532_ = lean_io_error_to_string(v_a_5527_);
                if v_isShared_5526_ == 0 {
                    lean_ctor_set_tag(v___x_5525_, 3);
                    lean_ctor_set(v___x_5525_, 0, v___x_5532_);
                    v___x_5534_ = v___x_5525_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5532_);
                    v___x_5534_ = v_reuseFailAlloc_5540_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_5535_ = l_Lean_MessageData_ofFormat(v___x_5534_);
                lean_inc(v_ref_5531_);
                v___x_5536_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5536_, 0, v_ref_5531_);
                lean_ctor_set(v___x_5536_, 1, v___x_5535_);
                if v_isShared_5530_ == 0 {
                    lean_ctor_set(v___x_5529_, 0, v___x_5536_);
                    v___x_5538_ = v___x_5529_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
                    v___x_5538_ = v_reuseFailAlloc_5539_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5538_;
            }
            34 => {
                if v_isShared_5547_ == 0 {
                    v___x_5549_ = v___x_5546_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5549_;
            }
            36 => {
                v_projName_5556_ = lean_ctor_get(v_i_5552_, 0);
                lean_inc(v_projName_5556_);
                lean_dec_ref(v_i_5552_);
                v___x_5557_ = 1;
                v___x_5558_ = l_Lean_findDocString_x3f(v_env_5375_, v_projName_5556_, v___x_5557_);
                if lean_obj_tag(v___x_5558_) == 0 {
                    lean_del_object(v___x_5554_);
                    v_a_5559_ = lean_ctor_get(v___x_5558_, 0);
                    v_isSharedCheck_5566_ = (!lean_is_exclusive(v___x_5558_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5561_ = v___x_5558_;
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_5559_);
                        lean_dec(v___x_5558_);
                        v___x_5561_ = lean_box(0);
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 37;
                        continue;
                    }
                } else {
                    v_a_5567_ = lean_ctor_get(v___x_5558_, 0);
                    v_isSharedCheck_5581_ = (!lean_is_exclusive(v___x_5558_)) as u8;
                    if v_isSharedCheck_5581_ == 0 {
                        v___x_5569_ = v___x_5558_;
                        v_isShared_5570_ = v_isSharedCheck_5581_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_5567_);
                        lean_dec(v___x_5558_);
                        v___x_5569_ = lean_box(0);
                        v_isShared_5570_ = v_isSharedCheck_5581_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_5562_ == 0 {
                    v___x_5564_ = v___x_5561_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
                    v___x_5564_ = v_reuseFailAlloc_5565_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5564_;
            }
            39 => {
                v_ref_5571_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5572_ = lean_io_error_to_string(v_a_5567_);
                if v_isShared_5555_ == 0 {
                    lean_ctor_set_tag(v___x_5554_, 3);
                    lean_ctor_set(v___x_5554_, 0, v___x_5572_);
                    v___x_5574_ = v___x_5554_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5572_);
                    v___x_5574_ = v_reuseFailAlloc_5580_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_5575_ = l_Lean_MessageData_ofFormat(v___x_5574_);
                lean_inc(v_ref_5571_);
                v___x_5576_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5576_, 0, v_ref_5571_);
                lean_ctor_set(v___x_5576_, 1, v___x_5575_);
                if v_isShared_5570_ == 0 {
                    lean_ctor_set(v___x_5569_, 0, v___x_5576_);
                    v___x_5578_ = v___x_5569_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5578_;
            }
            42 => {
                v_optionName_5587_ = lean_ctor_get(v_i_5583_, 1);
                lean_inc(v_optionName_5587_);
                v_declName_5588_ = lean_ctor_get(v_i_5583_, 2);
                lean_inc(v_declName_5588_);
                lean_dec_ref(v_i_5583_);
                v___x_5589_ = 1;
                v___x_5590_ = l_Lean_findDocString_x3f(v_env_5375_, v_declName_5588_, v___x_5589_);
                if lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5636_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5636_ == 0 {
                        v___x_5593_ = v___x_5590_;
                        v_isShared_5594_ = v_isSharedCheck_5636_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_5591_);
                        lean_dec(v___x_5590_);
                        v___x_5593_ = lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5636_;
                        state = 43;
                        continue;
                    }
                } else {
                    lean_dec(v_optionName_5587_);
                    v_a_5637_ = lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5651_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5651_ == 0 {
                        v___x_5639_ = v___x_5590_;
                        v_isShared_5640_ = v_isSharedCheck_5651_;
                        state = 53;
                        continue;
                    } else {
                        lean_inc(v_a_5637_);
                        lean_dec(v___x_5590_);
                        v___x_5639_ = lean_box(0);
                        v_isShared_5640_ = v_isSharedCheck_5651_;
                        state = 53;
                        continue;
                    }
                }
            }
            43 => {
                if lean_obj_tag(v_a_5591_) == 1 {
                    lean_dec(v_optionName_5587_);
                    lean_del_object(v___x_5585_);
                    if v_isShared_5594_ == 0 {
                        v___x_5596_ = v___x_5593_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
                        v___x_5596_ = v_reuseFailAlloc_5597_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5593_);
                    lean_dec(v_a_5591_);
                    v___x_5598_ = l_Lean_getOptionDecls();
                    if lean_obj_tag(v___x_5598_) == 0 {
                        lean_del_object(v___x_5585_);
                        v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
                        v_isSharedCheck_5620_ = (!lean_is_exclusive(v___x_5598_)) as u8;
                        if v_isSharedCheck_5620_ == 0 {
                            v___x_5601_ = v___x_5598_;
                            v_isShared_5602_ = v_isSharedCheck_5620_;
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_a_5599_);
                            lean_dec(v___x_5598_);
                            v___x_5601_ = lean_box(0);
                            v_isShared_5602_ = v_isSharedCheck_5620_;
                            state = 45;
                            continue;
                        }
                    } else {
                        lean_dec(v_optionName_5587_);
                        v_a_5621_ = lean_ctor_get(v___x_5598_, 0);
                        v_isSharedCheck_5635_ = (!lean_is_exclusive(v___x_5598_)) as u8;
                        if v_isSharedCheck_5635_ == 0 {
                            v___x_5623_ = v___x_5598_;
                            v_isShared_5624_ = v_isSharedCheck_5635_;
                            state = 50;
                            continue;
                        } else {
                            lean_inc(v_a_5621_);
                            lean_dec(v___x_5598_);
                            v___x_5623_ = lean_box(0);
                            v_isShared_5624_ = v_isSharedCheck_5635_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            44 => {
                return v___x_5596_;
            }
            45 => {
                v___x_5603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_5599_, v_optionName_5587_);
                lean_dec(v_optionName_5587_);
                lean_dec(v_a_5599_);
                if lean_obj_tag(v___x_5603_) == 1 {
                    v_val_5604_ = lean_ctor_get(v___x_5603_, 0);
                    v_isSharedCheck_5615_ = (!lean_is_exclusive(v___x_5603_)) as u8;
                    if v_isSharedCheck_5615_ == 0 {
                        v___x_5606_ = v___x_5603_;
                        v_isShared_5607_ = v_isSharedCheck_5615_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_val_5604_);
                        lean_dec(v___x_5603_);
                        v___x_5606_ = lean_box(0);
                        v_isShared_5607_ = v_isSharedCheck_5615_;
                        state = 46;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5603_);
                    v___x_5616_ = lean_box(0);
                    if v_isShared_5602_ == 0 {
                        lean_ctor_set(v___x_5601_, 0, v___x_5616_);
                        v___x_5618_ = v___x_5601_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5616_);
                        v___x_5618_ = v_reuseFailAlloc_5619_;
                        state = 49;
                        continue;
                    }
                }
            }
            46 => {
                v___x_5608_ = l_Lean_OptionDecl_fullDescr(v_val_5604_);
                if v_isShared_5607_ == 0 {
                    lean_ctor_set(v___x_5606_, 0, v___x_5608_);
                    v___x_5610_ = v___x_5606_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5608_);
                    v___x_5610_ = v_reuseFailAlloc_5614_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                if v_isShared_5602_ == 0 {
                    lean_ctor_set(v___x_5601_, 0, v___x_5610_);
                    v___x_5612_ = v___x_5601_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
                    v___x_5612_ = v_reuseFailAlloc_5613_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5612_;
            }
            49 => {
                return v___x_5618_;
            }
            50 => {
                v_ref_5625_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5626_ = lean_io_error_to_string(v_a_5621_);
                if v_isShared_5586_ == 0 {
                    lean_ctor_set_tag(v___x_5585_, 3);
                    lean_ctor_set(v___x_5585_, 0, v___x_5626_);
                    v___x_5628_ = v___x_5585_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5626_);
                    v___x_5628_ = v_reuseFailAlloc_5634_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_5629_ = l_Lean_MessageData_ofFormat(v___x_5628_);
                lean_inc(v_ref_5625_);
                v___x_5630_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5630_, 0, v_ref_5625_);
                lean_ctor_set(v___x_5630_, 1, v___x_5629_);
                if v_isShared_5624_ == 0 {
                    lean_ctor_set(v___x_5623_, 0, v___x_5630_);
                    v___x_5632_ = v___x_5623_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5630_);
                    v___x_5632_ = v_reuseFailAlloc_5633_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5632_;
            }
            53 => {
                v_ref_5641_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5642_ = lean_io_error_to_string(v_a_5637_);
                if v_isShared_5586_ == 0 {
                    lean_ctor_set_tag(v___x_5585_, 3);
                    lean_ctor_set(v___x_5585_, 0, v___x_5642_);
                    v___x_5644_ = v___x_5585_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5650_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5642_);
                    v___x_5644_ = v_reuseFailAlloc_5650_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_5645_ = l_Lean_MessageData_ofFormat(v___x_5644_);
                lean_inc(v_ref_5641_);
                v___x_5646_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5646_, 0, v_ref_5641_);
                lean_ctor_set(v___x_5646_, 1, v___x_5645_);
                if v_isShared_5640_ == 0 {
                    lean_ctor_set(v___x_5639_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5639_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
                    v___x_5648_ = v_reuseFailAlloc_5649_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_5648_;
            }
            56 => {
                if lean_obj_tag(v_a_5656_) == 1 {
                    v_val_5660_ = lean_ctor_get(v_a_5656_, 0);
                    v_isSharedCheck_5671_ = (!lean_is_exclusive(v_a_5656_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5662_ = v_a_5656_;
                        v_isShared_5663_ = v_isSharedCheck_5671_;
                        state = 57;
                        continue;
                    } else {
                        lean_inc(v_val_5660_);
                        lean_dec(v_a_5656_);
                        v___x_5662_ = lean_box(0);
                        v_isShared_5663_ = v_isSharedCheck_5671_;
                        state = 57;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5656_);
                    v___x_5672_ = lean_box(0);
                    if v_isShared_5659_ == 0 {
                        lean_ctor_set(v___x_5658_, 0, v___x_5672_);
                        v___x_5674_ = v___x_5658_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5672_);
                        v___x_5674_ = v_reuseFailAlloc_5675_;
                        state = 60;
                        continue;
                    }
                }
            }
            57 => {
                v___x_5664_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_5660_);
                lean_dec(v_val_5660_);
                if v_isShared_5663_ == 0 {
                    lean_ctor_set(v___x_5662_, 0, v___x_5664_);
                    v___x_5666_ = v___x_5662_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5664_);
                    v___x_5666_ = v_reuseFailAlloc_5670_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                if v_isShared_5659_ == 0 {
                    lean_ctor_set(v___x_5658_, 0, v___x_5666_);
                    v___x_5668_ = v___x_5658_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5666_);
                    v___x_5668_ = v_reuseFailAlloc_5669_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5668_;
            }
            60 => {
                return v___x_5674_;
            }
            61 => {
                v_stx_5681_ = lean_ctor_get(v_i_5677_, 1);
                v_isSharedCheck_5713_ = (!lean_is_exclusive(v_i_5677_)) as u8;
                if v_isSharedCheck_5713_ == 0 {
                    v_unused_5714_ = lean_ctor_get(v_i_5677_, 0);
                    lean_dec(v_unused_5714_);
                    v___x_5683_ = v_i_5677_;
                    v_isShared_5684_ = v_isSharedCheck_5713_;
                    state = 62;
                    continue;
                } else {
                    lean_inc(v_stx_5681_);
                    lean_dec(v_i_5677_);
                    v___x_5683_ = lean_box(0);
                    v_isShared_5684_ = v_isSharedCheck_5713_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v___x_5685_ = l_Lean_Syntax_getKind(v_stx_5681_);
                v___x_5686_ = 1;
                v___x_5687_ = l_Lean_findDocString_x3f(v_env_5375_, v___x_5685_, v___x_5686_);
                if lean_obj_tag(v___x_5687_) == 0 {
                    lean_del_object(v___x_5683_);
                    lean_del_object(v___x_5679_);
                    v_a_5688_ = lean_ctor_get(v___x_5687_, 0);
                    v_isSharedCheck_5695_ = (!lean_is_exclusive(v___x_5687_)) as u8;
                    if v_isSharedCheck_5695_ == 0 {
                        v___x_5690_ = v___x_5687_;
                        v_isShared_5691_ = v_isSharedCheck_5695_;
                        state = 63;
                        continue;
                    } else {
                        lean_inc(v_a_5688_);
                        lean_dec(v___x_5687_);
                        v___x_5690_ = lean_box(0);
                        v_isShared_5691_ = v_isSharedCheck_5695_;
                        state = 63;
                        continue;
                    }
                } else {
                    v_a_5696_ = lean_ctor_get(v___x_5687_, 0);
                    v_isSharedCheck_5712_ = (!lean_is_exclusive(v___x_5687_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5698_ = v___x_5687_;
                        v_isShared_5699_ = v_isSharedCheck_5712_;
                        state = 65;
                        continue;
                    } else {
                        lean_inc(v_a_5696_);
                        lean_dec(v___x_5687_);
                        v___x_5698_ = lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5712_;
                        state = 65;
                        continue;
                    }
                }
            }
            63 => {
                if v_isShared_5691_ == 0 {
                    v___x_5693_ = v___x_5690_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
                    v___x_5693_ = v_reuseFailAlloc_5694_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5693_;
            }
            65 => {
                v_ref_5700_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5701_ = lean_io_error_to_string(v_a_5696_);
                if v_isShared_5680_ == 0 {
                    lean_ctor_set_tag(v___x_5679_, 3);
                    lean_ctor_set(v___x_5679_, 0, v___x_5701_);
                    v___x_5703_ = v___x_5679_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_5711_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5701_);
                    v___x_5703_ = v_reuseFailAlloc_5711_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                v___x_5704_ = l_Lean_MessageData_ofFormat(v___x_5703_);
                lean_inc(v_ref_5700_);
                if v_isShared_5684_ == 0 {
                    lean_ctor_set(v___x_5683_, 1, v___x_5704_);
                    lean_ctor_set(v___x_5683_, 0, v_ref_5700_);
                    v___x_5706_ = v___x_5683_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_ref_5700_);
                    lean_ctor_set(v_reuseFailAlloc_5710_, 1, v___x_5704_);
                    v___x_5706_ = v_reuseFailAlloc_5710_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                if v_isShared_5699_ == 0 {
                    lean_ctor_set(v___x_5698_, 0, v___x_5706_);
                    v___x_5708_ = v___x_5698_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5706_);
                    v___x_5708_ = v_reuseFailAlloc_5709_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_5708_;
            }
            69 => {
                v_name_5720_ = lean_ctor_get(v_i_5716_, 1);
                lean_inc(v_name_5720_);
                lean_dec_ref(v_i_5716_);
                v___x_5721_ = 1;
                v___x_5722_ = l_Lean_findDocString_x3f(v_env_5375_, v_name_5720_, v___x_5721_);
                if lean_obj_tag(v___x_5722_) == 0 {
                    lean_del_object(v___x_5718_);
                    v_a_5723_ = lean_ctor_get(v___x_5722_, 0);
                    v_isSharedCheck_5730_ = (!lean_is_exclusive(v___x_5722_)) as u8;
                    if v_isSharedCheck_5730_ == 0 {
                        v___x_5725_ = v___x_5722_;
                        v_isShared_5726_ = v_isSharedCheck_5730_;
                        state = 70;
                        continue;
                    } else {
                        lean_inc(v_a_5723_);
                        lean_dec(v___x_5722_);
                        v___x_5725_ = lean_box(0);
                        v_isShared_5726_ = v_isSharedCheck_5730_;
                        state = 70;
                        continue;
                    }
                } else {
                    v_a_5731_ = lean_ctor_get(v___x_5722_, 0);
                    v_isSharedCheck_5745_ = (!lean_is_exclusive(v___x_5722_)) as u8;
                    if v_isSharedCheck_5745_ == 0 {
                        v___x_5733_ = v___x_5722_;
                        v_isShared_5734_ = v_isSharedCheck_5745_;
                        state = 72;
                        continue;
                    } else {
                        lean_inc(v_a_5731_);
                        lean_dec(v___x_5722_);
                        v___x_5733_ = lean_box(0);
                        v_isShared_5734_ = v_isSharedCheck_5745_;
                        state = 72;
                        continue;
                    }
                }
            }
            70 => {
                if v_isShared_5726_ == 0 {
                    v___x_5728_ = v___x_5725_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
                    v___x_5728_ = v_reuseFailAlloc_5729_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_5728_;
            }
            72 => {
                v_ref_5735_ = lean_ctor_get(v_a_5371_, 5);
                v___x_5736_ = lean_io_error_to_string(v_a_5731_);
                if v_isShared_5719_ == 0 {
                    lean_ctor_set_tag(v___x_5718_, 3);
                    lean_ctor_set(v___x_5718_, 0, v___x_5736_);
                    v___x_5738_ = v___x_5718_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_5744_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5744_, 0, v___x_5736_);
                    v___x_5738_ = v_reuseFailAlloc_5744_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                v___x_5739_ = l_Lean_MessageData_ofFormat(v___x_5738_);
                lean_inc(v_ref_5735_);
                v___x_5740_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5740_, 0, v_ref_5735_);
                lean_ctor_set(v___x_5740_, 1, v___x_5739_);
                if v_isShared_5734_ == 0 {
                    lean_ctor_set(v___x_5733_, 0, v___x_5740_);
                    v___x_5742_ = v___x_5733_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5740_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_5742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_docString_x3f___boxed(
    mut v_i_5747_: *mut LeanObject,
    mut v_a_5748_: *mut LeanObject,
    mut v_a_5749_: *mut LeanObject,
    mut v_a_5750_: *mut LeanObject,
    mut v_a_5751_: *mut LeanObject,
    mut v_a_5752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5753_: *mut LeanObject = core::ptr::null_mut();
    v_res_5753_ =
        l_Lean_Elab_Info_docString_x3f(v_i_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_);
    lean_dec(v_a_5751_);
    lean_dec_ref(v_a_5750_);
    lean_dec(v_a_5749_);
    lean_dec_ref(v_a_5748_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(
    mut v_msgData_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    v___x_5760_ = lean_st_ref_get(v___y_5758_);
    v_env_5761_ = lean_ctor_get(v___x_5760_, 0);
    lean_inc_ref(v_env_5761_);
    lean_dec(v___x_5760_);
    v___x_5762_ = lean_st_ref_get(v___y_5756_);
    v_mctx_5763_ = lean_ctor_get(v___x_5762_, 0);
    lean_inc_ref(v_mctx_5763_);
    lean_dec(v___x_5762_);
    v_lctx_5764_ = lean_ctor_get(v___y_5755_, 2);
    v_options_5765_ = lean_ctor_get(v___y_5757_, 2);
    lean_inc_ref(v_options_5765_);
    lean_inc_ref(v_lctx_5764_);
    v___x_5766_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5766_, 0, v_env_5761_);
    lean_ctor_set(v___x_5766_, 1, v_mctx_5763_);
    lean_ctor_set(v___x_5766_, 2, v_lctx_5764_);
    lean_ctor_set(v___x_5766_, 3, v_options_5765_);
    v___x_5767_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5767_, 0, v___x_5766_);
    lean_ctor_set(v___x_5767_, 1, v_msgData_5754_);
    v___x_5768_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5768_, 0, v___x_5767_);
    return v___x_5768_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5775_: *mut LeanObject = core::ptr::null_mut();
    v_res_5775_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
    lean_dec(v___y_5773_);
    lean_dec_ref(v___y_5772_);
    lean_dec(v___y_5771_);
    lean_dec_ref(v___y_5770_);
    return v_res_5775_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5782_ = lean_ctor_get(v___y_5779_, 5);
                v___x_5783_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
                v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
                v_isSharedCheck_5792_ = (!lean_is_exclusive(v___x_5783_)) as u8;
                if v_isSharedCheck_5792_ == 0 {
                    v___x_5786_ = v___x_5783_;
                    v_isShared_5787_ = v_isSharedCheck_5792_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5784_);
                    lean_dec(v___x_5783_);
                    v___x_5786_ = lean_box(0);
                    v_isShared_5787_ = v_isSharedCheck_5792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5782_);
                v___x_5788_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5788_, 0, v_ref_5782_);
                lean_ctor_set(v___x_5788_, 1, v_a_5784_);
                if v_isShared_5787_ == 0 {
                    lean_ctor_set_tag(v___x_5786_, 1);
                    lean_ctor_set(v___x_5786_, 0, v___x_5788_);
                    v___x_5790_ = v___x_5786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5791_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5788_);
                    v___x_5790_ = v_reuseFailAlloc_5791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5799_: *mut LeanObject = core::ptr::null_mut();
    v_res_5799_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_);
    lean_dec(v___y_5797_);
    lean_dec_ref(v___y_5796_);
    lean_dec(v___y_5795_);
    lean_dec_ref(v___y_5794_);
    return v_res_5799_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_ref_5800_: *mut LeanObject,
    mut v_msg_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5819_: u8 = 0;
    let mut v_cancelTk_x3f_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5821_: u8 = 0;
    let mut v_inheritedTraceOptions_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5807_ = lean_ctor_get(v___y_5804_, 0);
    v_fileMap_5808_ = lean_ctor_get(v___y_5804_, 1);
    v_options_5809_ = lean_ctor_get(v___y_5804_, 2);
    v_currRecDepth_5810_ = lean_ctor_get(v___y_5804_, 3);
    v_maxRecDepth_5811_ = lean_ctor_get(v___y_5804_, 4);
    v_ref_5812_ = lean_ctor_get(v___y_5804_, 5);
    v_currNamespace_5813_ = lean_ctor_get(v___y_5804_, 6);
    v_openDecls_5814_ = lean_ctor_get(v___y_5804_, 7);
    v_initHeartbeats_5815_ = lean_ctor_get(v___y_5804_, 8);
    v_maxHeartbeats_5816_ = lean_ctor_get(v___y_5804_, 9);
    v_quotContext_5817_ = lean_ctor_get(v___y_5804_, 10);
    v_currMacroScope_5818_ = lean_ctor_get(v___y_5804_, 11);
    v_diag_5819_ = lean_ctor_get_uint8(
        v___y_5804_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5820_ = lean_ctor_get(v___y_5804_, 12);
    v_suppressElabErrors_5821_ = lean_ctor_get_uint8(
        v___y_5804_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5822_ = lean_ctor_get(v___y_5804_, 13);
    v_ref_5823_ = l_Lean_replaceRef(v_ref_5800_, v_ref_5812_);
    lean_inc_ref(v_inheritedTraceOptions_5822_);
    lean_inc(v_cancelTk_x3f_5820_);
    lean_inc(v_currMacroScope_5818_);
    lean_inc(v_quotContext_5817_);
    lean_inc(v_maxHeartbeats_5816_);
    lean_inc(v_initHeartbeats_5815_);
    lean_inc(v_openDecls_5814_);
    lean_inc(v_currNamespace_5813_);
    lean_inc(v_maxRecDepth_5811_);
    lean_inc(v_currRecDepth_5810_);
    lean_inc_ref(v_options_5809_);
    lean_inc_ref(v_fileMap_5808_);
    lean_inc_ref(v_fileName_5807_);
    v___x_5824_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5824_, 0, v_fileName_5807_);
    lean_ctor_set(v___x_5824_, 1, v_fileMap_5808_);
    lean_ctor_set(v___x_5824_, 2, v_options_5809_);
    lean_ctor_set(v___x_5824_, 3, v_currRecDepth_5810_);
    lean_ctor_set(v___x_5824_, 4, v_maxRecDepth_5811_);
    lean_ctor_set(v___x_5824_, 5, v_ref_5823_);
    lean_ctor_set(v___x_5824_, 6, v_currNamespace_5813_);
    lean_ctor_set(v___x_5824_, 7, v_openDecls_5814_);
    lean_ctor_set(v___x_5824_, 8, v_initHeartbeats_5815_);
    lean_ctor_set(v___x_5824_, 9, v_maxHeartbeats_5816_);
    lean_ctor_set(v___x_5824_, 10, v_quotContext_5817_);
    lean_ctor_set(v___x_5824_, 11, v_currMacroScope_5818_);
    lean_ctor_set(v___x_5824_, 12, v_cancelTk_x3f_5820_);
    lean_ctor_set(v___x_5824_, 13, v_inheritedTraceOptions_5822_);
    lean_ctor_set_uint8(
        v___x_5824_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5819_,
    );
    lean_ctor_set_uint8(
        v___x_5824_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5821_,
    );
    v___x_5825_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_5801_, v___y_5802_, v___y_5803_, v___x_5824_, v___y_5805_);
    lean_dec_ref_known(v___x_5824_, 14);
    return v___x_5825_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_5826_: *mut LeanObject,
    mut v_msg_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
    mut v___y_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5833_: *mut LeanObject = core::ptr::null_mut();
    v_res_5833_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5826_, v_msg_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_);
    lean_dec(v___y_5831_);
    lean_dec_ref(v___y_5830_);
    lean_dec(v___y_5829_);
    lean_dec_ref(v___y_5828_);
    lean_dec(v_ref_5826_);
    return v_res_5833_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    v___x_5834_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5834_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    v___x_5835_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_5836_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5836_, 0, v___x_5835_);
    return v___x_5836_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    v___x_5837_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_5838_ = lean_unsigned_to_nat(0);
    v___x_5839_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5839_, 0, v___x_5838_);
    lean_ctor_set(v___x_5839_, 1, v___x_5838_);
    lean_ctor_set(v___x_5839_, 2, v___x_5838_);
    lean_ctor_set(v___x_5839_, 3, v___x_5838_);
    lean_ctor_set(v___x_5839_, 4, v___x_5837_);
    lean_ctor_set(v___x_5839_, 5, v___x_5837_);
    lean_ctor_set(v___x_5839_, 6, v___x_5837_);
    lean_ctor_set(v___x_5839_, 7, v___x_5837_);
    lean_ctor_set(v___x_5839_, 8, v___x_5837_);
    lean_ctor_set(v___x_5839_, 9, v___x_5837_);
    return v___x_5839_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    v___x_5840_ = lean_unsigned_to_nat(32);
    v___x_5841_ = lean_mk_empty_array_with_capacity(v___x_5840_);
    v___x_5842_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5842_, 0, v___x_5841_);
    return v___x_5842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5843_: usize = 0;
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    v___x_5843_ = 5usize;
    v___x_5844_ = lean_unsigned_to_nat(0);
    v___x_5845_ = lean_unsigned_to_nat(32);
    v___x_5846_ = lean_mk_empty_array_with_capacity(v___x_5845_);
    v___x_5847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_5848_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5848_, 0, v___x_5847_);
    lean_ctor_set(v___x_5848_, 1, v___x_5846_);
    lean_ctor_set(v___x_5848_, 2, v___x_5844_);
    lean_ctor_set(v___x_5848_, 3, v___x_5844_);
    lean_ctor_set_usize(v___x_5848_, 4, v___x_5843_);
    return v___x_5848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    v___x_5849_ = lean_box(1);
    v___x_5850_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_5851_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_5852_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5852_, 0, v___x_5851_);
    lean_ctor_set(v___x_5852_, 1, v___x_5850_);
    lean_ctor_set(v___x_5852_, 2, v___x_5849_);
    return v___x_5852_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    v___x_5854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_5855_ = l_Lean_stringToMessageData(v___x_5854_);
    return v___x_5855_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    v___x_5857_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_5858_ = l_Lean_stringToMessageData(v___x_5857_);
    return v___x_5858_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    v___x_5860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_5861_ = l_Lean_stringToMessageData(v___x_5860_);
    return v___x_5861_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    v___x_5863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_5864_ = l_Lean_stringToMessageData(v___x_5863_);
    return v___x_5864_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    v___x_5866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_5867_ = l_Lean_stringToMessageData(v___x_5866_);
    return v___x_5867_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    v___x_5869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_5870_ = l_Lean_stringToMessageData(v___x_5869_);
    return v___x_5870_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    v___x_5872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_5873_ = l_Lean_stringToMessageData(v___x_5872_);
    return v___x_5873_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_5874_: *mut LeanObject,
    mut v_declHint_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: u8 = 0;
    let mut v_isExporting_5881_: u8 = 0;
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: u8 = 0;
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: u8 = 0;
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5878_ = lean_st_ref_get(v___y_5876_);
                v_env_5879_ = lean_ctor_get(v___x_5878_, 0);
                lean_inc_ref(v_env_5879_);
                lean_dec(v___x_5878_);
                v___x_5880_ = l_Lean_Name_isAnonymous(v_declHint_5875_);
                if v___x_5880_ == 0 {
                    v_isExporting_5881_ = lean_ctor_get_uint8(
                        v_env_5879_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5881_ == 0 {
                        lean_dec_ref(v_env_5879_);
                        lean_dec(v_declHint_5875_);
                        v___x_5882_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5882_, 0, v_msg_5874_);
                        return v___x_5882_;
                    } else {
                        lean_inc_ref(v_env_5879_);
                        v___x_5883_ = l_Lean_Environment_setExporting(v_env_5879_, v___x_5880_);
                        lean_inc(v_declHint_5875_);
                        lean_inc_ref(v___x_5883_);
                        v___x_5884_ = l_Lean_Environment_contains(
                            v___x_5883_,
                            v_declHint_5875_,
                            v_isExporting_5881_,
                        );
                        if v___x_5884_ == 0 {
                            lean_dec_ref(v___x_5883_);
                            lean_dec_ref(v_env_5879_);
                            lean_dec(v_declHint_5875_);
                            v___x_5885_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5885_, 0, v_msg_5874_);
                            return v___x_5885_;
                        } else {
                            v___x_5886_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_5887_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_5888_ = l_Lean_Options_empty;
                            v___x_5889_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5889_, 0, v___x_5883_);
                            lean_ctor_set(v___x_5889_, 1, v___x_5886_);
                            lean_ctor_set(v___x_5889_, 2, v___x_5887_);
                            lean_ctor_set(v___x_5889_, 3, v___x_5888_);
                            lean_inc(v_declHint_5875_);
                            v___x_5890_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5875_, v___x_5880_);
                            v_c_5891_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_5891_, 0, v___x_5889_);
                            lean_ctor_set(v_c_5891_, 1, v___x_5890_);
                            v___x_5892_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5879_,
                                v_declHint_5875_,
                            );
                            if lean_obj_tag(v___x_5892_) == 0 {
                                lean_dec_ref(v_env_5879_);
                                lean_dec(v_declHint_5875_);
                                v___x_5893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_5894_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5894_, 0, v___x_5893_);
                                lean_ctor_set(v___x_5894_, 1, v_c_5891_);
                                v___x_5895_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_5896_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5896_, 0, v___x_5894_);
                                lean_ctor_set(v___x_5896_, 1, v___x_5895_);
                                v___x_5897_ = l_Lean_MessageData_note(v___x_5896_);
                                v___x_5898_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5898_, 0, v_msg_5874_);
                                lean_ctor_set(v___x_5898_, 1, v___x_5897_);
                                v___x_5899_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_5899_, 0, v___x_5898_);
                                return v___x_5899_;
                            } else {
                                v_val_5900_ = lean_ctor_get(v___x_5892_, 0);
                                v_isSharedCheck_5935_ = (!lean_is_exclusive(v___x_5892_)) as u8;
                                if v_isSharedCheck_5935_ == 0 {
                                    v___x_5902_ = v___x_5892_;
                                    v_isShared_5903_ = v_isSharedCheck_5935_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5900_);
                                    lean_dec(v___x_5892_);
                                    v___x_5902_ = lean_box(0);
                                    v_isShared_5903_ = v_isSharedCheck_5935_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_5879_);
                    lean_dec(v_declHint_5875_);
                    v___x_5936_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5936_, 0, v_msg_5874_);
                    return v___x_5936_;
                }
            }
            1 => {
                v___x_5904_ = lean_box(0);
                v___x_5905_ = l_Lean_Environment_header(v_env_5879_);
                lean_dec_ref(v_env_5879_);
                v___x_5906_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5905_);
                v_mod_5907_ = lean_array_get(v___x_5904_, v___x_5906_, v_val_5900_);
                lean_dec(v_val_5900_);
                lean_dec_ref(v___x_5906_);
                v___x_5908_ = l_Lean_isPrivateName(v_declHint_5875_);
                lean_dec(v_declHint_5875_);
                if v___x_5908_ == 0 {
                    v___x_5909_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_5910_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5910_, 0, v___x_5909_);
                    lean_ctor_set(v___x_5910_, 1, v_c_5891_);
                    v___x_5911_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_5912_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5912_, 0, v___x_5910_);
                    lean_ctor_set(v___x_5912_, 1, v___x_5911_);
                    v___x_5913_ = l_Lean_MessageData_ofName(v_mod_5907_);
                    v___x_5914_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5914_, 0, v___x_5912_);
                    lean_ctor_set(v___x_5914_, 1, v___x_5913_);
                    v___x_5915_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_5916_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5916_, 0, v___x_5914_);
                    lean_ctor_set(v___x_5916_, 1, v___x_5915_);
                    v___x_5917_ = l_Lean_MessageData_note(v___x_5916_);
                    v___x_5918_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5918_, 0, v_msg_5874_);
                    lean_ctor_set(v___x_5918_, 1, v___x_5917_);
                    if v_isShared_5903_ == 0 {
                        lean_ctor_set_tag(v___x_5902_, 0);
                        lean_ctor_set(v___x_5902_, 0, v___x_5918_);
                        v___x_5920_ = v___x_5902_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
                        v___x_5920_ = v_reuseFailAlloc_5921_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5922_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_5923_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5923_, 0, v___x_5922_);
                    lean_ctor_set(v___x_5923_, 1, v_c_5891_);
                    v___x_5924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_5925_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5925_, 0, v___x_5923_);
                    lean_ctor_set(v___x_5925_, 1, v___x_5924_);
                    v___x_5926_ = l_Lean_MessageData_ofName(v_mod_5907_);
                    v___x_5927_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5927_, 0, v___x_5925_);
                    lean_ctor_set(v___x_5927_, 1, v___x_5926_);
                    v___x_5928_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_5929_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5929_, 0, v___x_5927_);
                    lean_ctor_set(v___x_5929_, 1, v___x_5928_);
                    v___x_5930_ = l_Lean_MessageData_note(v___x_5929_);
                    v___x_5931_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5931_, 0, v_msg_5874_);
                    lean_ctor_set(v___x_5931_, 1, v___x_5930_);
                    if v_isShared_5903_ == 0 {
                        lean_ctor_set_tag(v___x_5902_, 0);
                        lean_ctor_set(v___x_5902_, 0, v___x_5931_);
                        v___x_5933_ = v___x_5902_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5934_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5934_, 0, v___x_5931_);
                        v___x_5933_ = v_reuseFailAlloc_5934_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5920_;
            }
            3 => {
                return v___x_5933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_5937_: *mut LeanObject,
    mut v_declHint_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5941_: *mut LeanObject = core::ptr::null_mut();
    v_res_5941_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5937_, v_declHint_5938_, v___y_5939_);
    lean_dec(v___y_5939_);
    return v_res_5941_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_5942_: *mut LeanObject,
    mut v_declHint_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5953_: u8 = 0;
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5942_, v_declHint_5943_, v___y_5947_);
                v_a_5950_ = lean_ctor_get(v___x_5949_, 0);
                v_isSharedCheck_5959_ = (!lean_is_exclusive(v___x_5949_)) as u8;
                if v_isSharedCheck_5959_ == 0 {
                    v___x_5952_ = v___x_5949_;
                    v_isShared_5953_ = v_isSharedCheck_5959_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5950_);
                    lean_dec(v___x_5949_);
                    v___x_5952_ = lean_box(0);
                    v_isShared_5953_ = v_isSharedCheck_5959_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5954_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5955_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_5955_, 0, v___x_5954_);
                lean_ctor_set(v___x_5955_, 1, v_a_5950_);
                if v_isShared_5953_ == 0 {
                    lean_ctor_set(v___x_5952_, 0, v___x_5955_);
                    v___x_5957_ = v___x_5952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5958_, 0, v___x_5955_);
                    v___x_5957_ = v_reuseFailAlloc_5958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_5960_: *mut LeanObject,
    mut v_declHint_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
    mut v___y_5963_: *mut LeanObject,
    mut v___y_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5967_: *mut LeanObject = core::ptr::null_mut();
    v_res_5967_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_5960_, v_declHint_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_);
    lean_dec(v___y_5965_);
    lean_dec_ref(v___y_5964_);
    lean_dec(v___y_5963_);
    lean_dec_ref(v___y_5962_);
    return v_res_5967_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_ref_5968_: *mut LeanObject,
    mut v_msg_5969_: *mut LeanObject,
    mut v_declHint_5970_: *mut LeanObject,
    mut v___y_5971_: *mut LeanObject,
    mut v___y_5972_: *mut LeanObject,
    mut v___y_5973_: *mut LeanObject,
    mut v___y_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    v___x_5976_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_5969_, v_declHint_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_);
    v_a_5977_ = lean_ctor_get(v___x_5976_, 0);
    lean_inc(v_a_5977_);
    lean_dec_ref(v___x_5976_);
    v___x_5978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5968_, v_a_5977_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_);
    return v___x_5978_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_5979_: *mut LeanObject,
    mut v_msg_5980_: *mut LeanObject,
    mut v_declHint_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
    mut v___y_5986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5987_: *mut LeanObject = core::ptr::null_mut();
    v_res_5987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_5979_, v_msg_5980_, v_declHint_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_);
    lean_dec(v___y_5985_);
    lean_dec_ref(v___y_5984_);
    lean_dec(v___y_5983_);
    lean_dec_ref(v___y_5982_);
    lean_dec(v_ref_5979_);
    return v_res_5987_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
    v___x_5990_ = l_Lean_stringToMessageData(v___x_5989_);
    return v___x_5990_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    v___x_5992_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
    v___x_5993_ = l_Lean_stringToMessageData(v___x_5992_);
    return v___x_5993_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_5994_: *mut LeanObject,
    mut v_constName_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: u8 = 0;
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    v___x_6001_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
    v___x_6002_ = 0;
    lean_inc(v_constName_5995_);
    v___x_6003_ = l_Lean_MessageData_ofConstName(v_constName_5995_, v___x_6002_);
    v___x_6004_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6004_, 0, v___x_6001_);
    lean_ctor_set(v___x_6004_, 1, v___x_6003_);
    v___x_6005_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
    v___x_6006_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6006_, 0, v___x_6004_);
    lean_ctor_set(v___x_6006_, 1, v___x_6005_);
    v___x_6007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_5994_, v___x_6006_, v_constName_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_);
    return v___x_6007_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_6008_: *mut LeanObject,
    mut v_constName_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6015_: *mut LeanObject = core::ptr::null_mut();
    v_res_6015_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6008_, v_constName_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_);
    lean_dec(v___y_6013_);
    lean_dec_ref(v___y_6012_);
    lean_dec(v___y_6011_);
    lean_dec_ref(v___y_6010_);
    lean_dec(v_ref_6008_);
    return v_res_6015_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_constName_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
    mut v___y_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    v_ref_6022_ = lean_ctor_get(v___y_6019_, 5);
    v___x_6023_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6022_, v_constName_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
    return v___x_6023_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6030_: *mut LeanObject = core::ptr::null_mut();
    v_res_6030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_);
    lean_dec(v___y_6028_);
    lean_dec_ref(v___y_6027_);
    lean_dec(v___y_6026_);
    lean_dec_ref(v___y_6025_);
    return v_res_6030_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(
    mut v_constName_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6045_: u8 = 0;
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6037_ = lean_st_ref_get(v___y_6035_);
                v_env_6038_ = lean_ctor_get(v___x_6037_, 0);
                lean_inc_ref(v_env_6038_);
                lean_dec(v___x_6037_);
                v___x_6039_ = 0;
                lean_inc(v_constName_6031_);
                v___x_6040_ =
                    l_Lean_Environment_find_x3f(v_env_6038_, v_constName_6031_, v___x_6039_);
                if lean_obj_tag(v___x_6040_) == 0 {
                    v___x_6041_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_);
                    return v___x_6041_;
                } else {
                    lean_dec(v_constName_6031_);
                    v_val_6042_ = lean_ctor_get(v___x_6040_, 0);
                    v_isSharedCheck_6049_ = (!lean_is_exclusive(v___x_6040_)) as u8;
                    if v_isSharedCheck_6049_ == 0 {
                        v___x_6044_ = v___x_6040_;
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6042_);
                        lean_dec(v___x_6040_);
                        v___x_6044_ = lean_box(0);
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6045_ == 0 {
                    lean_ctor_set_tag(v___x_6044_, 0);
                    v___x_6047_ = v___x_6044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_val_6042_);
                    v___x_6047_ = v_reuseFailAlloc_6048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(
    mut v_constName_6050_: *mut LeanObject,
    mut v___y_6051_: *mut LeanObject,
    mut v___y_6052_: *mut LeanObject,
    mut v___y_6053_: *mut LeanObject,
    mut v___y_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6056_: *mut LeanObject = core::ptr::null_mut();
    v_res_6056_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
    lean_dec(v___y_6054_);
    lean_dec_ref(v___y_6053_);
    lean_dec(v___y_6052_);
    lean_dec_ref(v___y_6051_);
    return v_res_6056_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(
    mut v_declName_6057_: *mut LeanObject,
    mut v___y_6058_: *mut LeanObject,
    mut v___y_6059_: *mut LeanObject,
    mut v___y_6060_: *mut LeanObject,
    mut v___y_6061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6066_: u8 = 0;
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6089_: u8 = 0;
    let mut v_isSharedCheck_6090_: u8 = 0;
    let mut v_unused_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_6057_);
                v___x_6063_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
                if lean_obj_tag(v___x_6063_) == 0 {
                    v_isSharedCheck_6090_ = (!lean_is_exclusive(v___x_6063_)) as u8;
                    if v_isSharedCheck_6090_ == 0 {
                        v_unused_6091_ = lean_ctor_get(v___x_6063_, 0);
                        lean_dec(v_unused_6091_);
                        v___x_6065_ = v___x_6063_;
                        v_isShared_6066_ = v_isSharedCheck_6090_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6063_);
                        v___x_6065_ = lean_box(0);
                        v_isShared_6066_ = v_isSharedCheck_6090_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_6057_);
                    v_a_6092_ = lean_ctor_get(v___x_6063_, 0);
                    v_isSharedCheck_6099_ = (!lean_is_exclusive(v___x_6063_)) as u8;
                    if v_isSharedCheck_6099_ == 0 {
                        v___x_6094_ = v___x_6063_;
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6092_);
                        lean_dec(v___x_6063_);
                        v___x_6094_ = lean_box(0);
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6067_ = lean_st_ref_get(v___y_6061_);
                v_env_6068_ = lean_ctor_get(v___x_6067_, 0);
                lean_inc_ref(v_env_6068_);
                lean_dec(v___x_6067_);
                v___x_6069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6068_, v_declName_6057_);
                lean_dec(v_declName_6057_);
                lean_dec_ref(v_env_6068_);
                if lean_obj_tag(v___x_6069_) == 0 {
                    v___x_6070_ = lean_box(0);
                    if v_isShared_6066_ == 0 {
                        lean_ctor_set(v___x_6065_, 0, v___x_6070_);
                        v___x_6072_ = v___x_6065_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6073_, 0, v___x_6070_);
                        v___x_6072_ = v_reuseFailAlloc_6073_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_6074_ = lean_ctor_get(v___x_6069_, 0);
                    v_isSharedCheck_6089_ = (!lean_is_exclusive(v___x_6069_)) as u8;
                    if v_isSharedCheck_6089_ == 0 {
                        v___x_6076_ = v___x_6069_;
                        v_isShared_6077_ = v_isSharedCheck_6089_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_6074_);
                        lean_dec(v___x_6069_);
                        v___x_6076_ = lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6089_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6072_;
            }
            3 => {
                v___x_6078_ = lean_st_ref_get(v___y_6061_);
                v_env_6079_ = lean_ctor_get(v___x_6078_, 0);
                lean_inc_ref(v_env_6079_);
                lean_dec(v___x_6078_);
                v___x_6080_ = lean_box(0);
                v___x_6081_ = l_Lean_Environment_allImportedModuleNames(v_env_6079_);
                lean_dec_ref(v_env_6079_);
                v___x_6082_ = lean_array_get(v___x_6080_, v___x_6081_, v_val_6074_);
                lean_dec(v_val_6074_);
                lean_dec_ref(v___x_6081_);
                if v_isShared_6077_ == 0 {
                    lean_ctor_set(v___x_6076_, 0, v___x_6082_);
                    v___x_6084_ = v___x_6076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6088_, 0, v___x_6082_);
                    v___x_6084_ = v_reuseFailAlloc_6088_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6066_ == 0 {
                    lean_ctor_set(v___x_6065_, 0, v___x_6084_);
                    v___x_6086_ = v___x_6065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6084_);
                    v___x_6086_ = v_reuseFailAlloc_6087_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6086_;
            }
            6 => {
                if v_isShared_6095_ == 0 {
                    v___x_6097_ = v___x_6094_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(
    mut v_declName_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
    mut v___y_6104_: *mut LeanObject,
    mut v___y_6105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6106_: *mut LeanObject = core::ptr::null_mut();
    v_res_6106_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_6100_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_);
    lean_dec(v___y_6104_);
    lean_dec_ref(v___y_6103_);
    lean_dec(v___y_6102_);
    lean_dec_ref(v___y_6101_);
    return v_res_6106_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(
    mut v_decl_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
    mut v_a_6115_: *mut LeanObject,
    mut v_a_6116_: *mut LeanObject,
    mut v_a_6117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v_val_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: u8 = 0;
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6146_: u8 = 0;
    let mut v_a_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6150_: u8 = 0;
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6119_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_);
                if lean_obj_tag(v___x_6119_) == 0 {
                    v_a_6120_ = lean_ctor_get(v___x_6119_, 0);
                    v_isSharedCheck_6146_ = (!lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6146_ == 0 {
                        v___x_6122_ = v___x_6119_;
                        v_isShared_6123_ = v_isSharedCheck_6146_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6120_);
                        lean_dec(v___x_6119_);
                        v___x_6122_ = lean_box(0);
                        v_isShared_6123_ = v_isSharedCheck_6146_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6147_ = lean_ctor_get(v___x_6119_, 0);
                    v_isSharedCheck_6154_ = (!lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6154_ == 0 {
                        v___x_6149_ = v___x_6119_;
                        v_isShared_6150_ = v_isSharedCheck_6154_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6147_);
                        lean_dec(v___x_6119_);
                        v___x_6149_ = lean_box(0);
                        v_isShared_6150_ = v_isSharedCheck_6154_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6120_) == 1 {
                    v_val_6124_ = lean_ctor_get(v_a_6120_, 0);
                    v_isSharedCheck_6141_ = (!lean_is_exclusive(v_a_6120_)) as u8;
                    if v_isSharedCheck_6141_ == 0 {
                        v___x_6126_ = v_a_6120_;
                        v_isShared_6127_ = v_isSharedCheck_6141_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_6124_);
                        lean_dec(v_a_6120_);
                        v___x_6126_ = lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6141_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6120_);
                    v___x_6142_ = lean_box(0);
                    if v_isShared_6123_ == 0 {
                        lean_ctor_set(v___x_6122_, 0, v___x_6142_);
                        v___x_6144_ = v___x_6122_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6145_, 0, v___x_6142_);
                        v___x_6144_ = v_reuseFailAlloc_6145_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6128_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1;
                v___x_6129_ = 1;
                v___x_6130_ = l_Lean_Name_toString(v_val_6124_, v___x_6129_);
                v___x_6131_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6131_, 0, v___x_6130_);
                v___x_6132_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6132_, 0, v___x_6128_);
                lean_ctor_set(v___x_6132_, 1, v___x_6131_);
                v___x_6133_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3;
                v___x_6134_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6134_, 0, v___x_6132_);
                lean_ctor_set(v___x_6134_, 1, v___x_6133_);
                if v_isShared_6127_ == 0 {
                    lean_ctor_set(v___x_6126_, 0, v___x_6134_);
                    v___x_6136_ = v___x_6126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6140_, 0, v___x_6134_);
                    v___x_6136_ = v_reuseFailAlloc_6140_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6123_ == 0 {
                    lean_ctor_set(v___x_6122_, 0, v___x_6136_);
                    v___x_6138_ = v___x_6122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6139_, 0, v___x_6136_);
                    v___x_6138_ = v_reuseFailAlloc_6139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6138_;
            }
            5 => {
                return v___x_6144_;
            }
            6 => {
                if v_isShared_6150_ == 0 {
                    v___x_6152_ = v___x_6149_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6153_, 0, v_a_6147_);
                    v___x_6152_ = v_reuseFailAlloc_6153_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(
    mut v_decl_6155_: *mut LeanObject,
    mut v_a_6156_: *mut LeanObject,
    mut v_a_6157_: *mut LeanObject,
    mut v_a_6158_: *mut LeanObject,
    mut v_a_6159_: *mut LeanObject,
    mut v_a_6160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6161_: *mut LeanObject = core::ptr::null_mut();
    v_res_6161_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(
        v_decl_6155_,
        v_a_6156_,
        v_a_6157_,
        v_a_6158_,
        v_a_6159_,
    );
    lean_dec(v_a_6159_);
    lean_dec_ref(v_a_6158_);
    lean_dec(v_a_6157_);
    lean_dec_ref(v_a_6156_);
    return v_res_6161_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_6162_: *mut LeanObject,
    mut v_constName_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    v___x_6169_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
    return v___x_6169_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_6170_: *mut LeanObject,
    mut v_constName_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6177_: *mut LeanObject = core::ptr::null_mut();
    v_res_6177_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_6170_, v_constName_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_);
    lean_dec(v___y_6175_);
    lean_dec_ref(v___y_6174_);
    lean_dec(v___y_6173_);
    lean_dec_ref(v___y_6172_);
    return v_res_6177_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6178_: *mut LeanObject,
    mut v_ref_6179_: *mut LeanObject,
    mut v_constName_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
    mut v___y_6183_: *mut LeanObject,
    mut v___y_6184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    v___x_6186_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6179_, v_constName_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_);
    return v___x_6186_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6187_: *mut LeanObject,
    mut v_ref_6188_: *mut LeanObject,
    mut v_constName_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6195_: *mut LeanObject = core::ptr::null_mut();
    v_res_6195_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6187_, v_ref_6188_, v_constName_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
    lean_dec(v___y_6193_);
    lean_dec_ref(v___y_6192_);
    lean_dec(v___y_6191_);
    lean_dec_ref(v___y_6190_);
    lean_dec(v_ref_6188_);
    return v_res_6195_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b1_6196_: *mut LeanObject,
    mut v_ref_6197_: *mut LeanObject,
    mut v_msg_6198_: *mut LeanObject,
    mut v_declHint_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    v___x_6205_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_6197_, v_msg_6198_, v_declHint_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
    return v___x_6205_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_6206_: *mut LeanObject,
    mut v_ref_6207_: *mut LeanObject,
    mut v_msg_6208_: *mut LeanObject,
    mut v_declHint_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
    mut v___y_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6215_: *mut LeanObject = core::ptr::null_mut();
    v_res_6215_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_6206_, v_ref_6207_, v_msg_6208_, v_declHint_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
    lean_dec(v___y_6213_);
    lean_dec_ref(v___y_6212_);
    lean_dec(v___y_6211_);
    lean_dec_ref(v___y_6210_);
    lean_dec(v_ref_6207_);
    return v_res_6215_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_6216_: *mut LeanObject,
    mut v_declHint_6217_: *mut LeanObject,
    mut v___y_6218_: *mut LeanObject,
    mut v___y_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
    mut v___y_6221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    v___x_6223_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_6216_, v_declHint_6217_, v___y_6221_);
    return v___x_6223_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_6224_: *mut LeanObject,
    mut v_declHint_6225_: *mut LeanObject,
    mut v___y_6226_: *mut LeanObject,
    mut v___y_6227_: *mut LeanObject,
    mut v___y_6228_: *mut LeanObject,
    mut v___y_6229_: *mut LeanObject,
    mut v___y_6230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6231_: *mut LeanObject = core::ptr::null_mut();
    v_res_6231_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_6224_, v_declHint_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_);
    lean_dec(v___y_6229_);
    lean_dec_ref(v___y_6228_);
    lean_dec(v___y_6227_);
    lean_dec_ref(v___y_6226_);
    return v_res_6231_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_6232_: *mut LeanObject,
    mut v_ref_6233_: *mut LeanObject,
    mut v_msg_6234_: *mut LeanObject,
    mut v___y_6235_: *mut LeanObject,
    mut v___y_6236_: *mut LeanObject,
    mut v___y_6237_: *mut LeanObject,
    mut v___y_6238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    v___x_6240_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_6233_, v_msg_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
    return v___x_6240_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_6241_: *mut LeanObject,
    mut v_ref_6242_: *mut LeanObject,
    mut v_msg_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
    mut v___y_6248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6249_: *mut LeanObject = core::ptr::null_mut();
    v_res_6249_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_6241_, v_ref_6242_, v_msg_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
    lean_dec(v___y_6247_);
    lean_dec_ref(v___y_6246_);
    lean_dec(v___y_6245_);
    lean_dec_ref(v___y_6244_);
    lean_dec(v_ref_6242_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_6250_: *mut LeanObject,
    mut v_msg_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    v___x_6257_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
    return v___x_6257_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_6258_: *mut LeanObject,
    mut v_msg_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6265_: *mut LeanObject = core::ptr::null_mut();
    v_res_6265_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_6258_, v_msg_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
    lean_dec(v___y_6263_);
    lean_dec_ref(v___y_6262_);
    lean_dec(v___y_6261_);
    lean_dec_ref(v___y_6260_);
    return v_res_6265_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(
    mut v_a_6266_: *mut LeanObject,
) -> u8 {
    let mut v___x_6267_: u8 = 0;
    let mut v_a_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_6266_) {
                3 => {
                    v___x_6267_ = 1;
                    return v___x_6267_;
                }
                6 => {
                    v_a_6268_ = lean_ctor_get(v_a_6266_, 0);
                    v_a_6266_ = v_a_6268_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_f_6270_ = lean_ctor_get(v_a_6266_, 1);
                    v_a_6266_ = v_f_6270_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_a_6272_ = lean_ctor_get(v_a_6266_, 1);
                    v_a_6266_ = v_a_6272_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_6274_ = 0;
                    return v___x_6274_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(
    mut v_a_6275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6276_: u8 = 0;
    let mut v_r_6277_: *mut LeanObject = core::ptr::null_mut();
    v_res_6276_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_6275_);
    lean_dec(v_a_6275_);
    v_r_6277_ = lean_box((v_res_6276_) as usize);
    return v_r_6277_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(
    mut v_e_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_unused_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6281_ = l_Lean_Expr_hasMVar(v_e_6278_);
                if v___x_6281_ == 0 {
                    v___x_6282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6282_, 0, v_e_6278_);
                    return v___x_6282_;
                } else {
                    v___x_6283_ = lean_st_ref_get(v___y_6279_);
                    v_mctx_6284_ = lean_ctor_get(v___x_6283_, 0);
                    lean_inc_ref(v_mctx_6284_);
                    lean_dec(v___x_6283_);
                    v___x_6285_ = l_Lean_instantiateMVarsCore(v_mctx_6284_, v_e_6278_);
                    v_fst_6286_ = lean_ctor_get(v___x_6285_, 0);
                    lean_inc(v_fst_6286_);
                    v_snd_6287_ = lean_ctor_get(v___x_6285_, 1);
                    lean_inc(v_snd_6287_);
                    lean_dec_ref(v___x_6285_);
                    v___x_6288_ = lean_st_ref_take(v___y_6279_);
                    v_cache_6289_ = lean_ctor_get(v___x_6288_, 1);
                    v_zetaDeltaFVarIds_6290_ = lean_ctor_get(v___x_6288_, 2);
                    v_postponed_6291_ = lean_ctor_get(v___x_6288_, 3);
                    v_diag_6292_ = lean_ctor_get(v___x_6288_, 4);
                    v_isSharedCheck_6301_ = (!lean_is_exclusive(v___x_6288_)) as u8;
                    if v_isSharedCheck_6301_ == 0 {
                        v_unused_6302_ = lean_ctor_get(v___x_6288_, 0);
                        lean_dec(v_unused_6302_);
                        v___x_6294_ = v___x_6288_;
                        v_isShared_6295_ = v_isSharedCheck_6301_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_6292_);
                        lean_inc(v_postponed_6291_);
                        lean_inc(v_zetaDeltaFVarIds_6290_);
                        lean_inc(v_cache_6289_);
                        lean_dec(v___x_6288_);
                        v___x_6294_ = lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6301_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6295_ == 0 {
                    lean_ctor_set(v___x_6294_, 0, v_snd_6287_);
                    v___x_6297_ = v___x_6294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_snd_6287_);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 1, v_cache_6289_);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 2, v_zetaDeltaFVarIds_6290_);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 3, v_postponed_6291_);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 4, v_diag_6292_);
                    v___x_6297_ = v_reuseFailAlloc_6300_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6298_ = lean_st_ref_set(v___y_6279_, v___x_6297_);
                v___x_6299_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6299_, 0, v_fst_6286_);
                return v___x_6299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(
    mut v_e_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6306_: *mut LeanObject = core::ptr::null_mut();
    v_res_6306_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_6303_, v___y_6304_);
    lean_dec(v___y_6304_);
    return v_res_6306_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(
    mut v_e_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
    mut v___y_6309_: *mut LeanObject,
    mut v___y_6310_: *mut LeanObject,
    mut v___y_6311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    v___x_6313_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_6307_, v___y_6309_);
    return v___x_6313_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(
    mut v_e_6314_: *mut LeanObject,
    mut v___y_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
    mut v___y_6317_: *mut LeanObject,
    mut v___y_6318_: *mut LeanObject,
    mut v___y_6319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6320_: *mut LeanObject = core::ptr::null_mut();
    v_res_6320_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_);
    lean_dec(v___y_6318_);
    lean_dec_ref(v___y_6317_);
    lean_dec(v___y_6316_);
    lean_dec_ref(v___y_6315_);
    return v_res_6320_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(
    mut v_i_6332_: *mut LeanObject,
    mut v_a_6333_: *mut LeanObject,
    mut v_a_6334_: *mut LeanObject,
    mut v_a_6335_: *mut LeanObject,
    mut v_a_6336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDisplayableTerm_6340_: u8 = 0;
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6345_: u8 = 0;
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6353_: u8 = 0;
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6362_: u8 = 0;
    let mut v_fmt_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infos_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6367_: u8 = 0;
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6382_: u8 = 0;
    let mut v_isSharedCheck_6383_: u8 = 0;
    let mut v_a_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6387_: u8 = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6391_: u8 = 0;
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v_a_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6405_: u8 = 0;
    let mut v___y_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6427_: u8 = 0;
    let mut v_lctx_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: u8 = 0;
    let mut v___x_6433_: u8 = 0;
    let mut v_isSharedCheck_6434_: u8 = 0;
    let mut v_a_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6438_: u8 = 0;
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6442_: u8 = 0;
    let mut v_a_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut v_isSharedCheck_6451_: u8 = 0;
    let mut v_a_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6455_: u8 = 0;
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6459_: u8 = 0;
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6464_: u8 = 0;
    let mut v_i_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6468_: u8 = 0;
    let mut v_fieldName_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: u8 = 0;
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6498_: u8 = 0;
    let mut v_a_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6502_: u8 = 0;
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6506_: u8 = 0;
    let mut v_a_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6510_: u8 = 0;
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6514_: u8 = 0;
    let mut v_isSharedCheck_6515_: u8 = 0;
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_i_6332_) {
                1 => {
                    v_i_6338_ = lean_ctor_get(v_i_6332_, 0);
                    lean_inc_ref(v_i_6338_);
                    lean_dec_ref_known(v_i_6332_, 1);
                    v_expr_6339_ = lean_ctor_get(v_i_6338_, 3);
                    lean_inc_ref(v_expr_6339_);
                    v_isDisplayableTerm_6340_ = lean_ctor_get_uint8(
                        v_i_6338_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    lean_dec_ref(v_i_6338_);
                    v___x_6341_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_6339_, v_a_6334_);
                    v_a_6342_ = lean_ctor_get(v___x_6341_, 0);
                    v_isSharedCheck_6464_ = (!lean_is_exclusive(v___x_6341_)) as u8;
                    if v_isSharedCheck_6464_ == 0 {
                        v___x_6344_ = v___x_6341_;
                        v_isShared_6345_ = v_isSharedCheck_6464_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6342_);
                        lean_dec(v___x_6341_);
                        v___x_6344_ = lean_box(0);
                        v_isShared_6345_ = v_isSharedCheck_6464_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_i_6465_ = lean_ctor_get(v_i_6332_, 0);
                    v_isSharedCheck_6515_ = (!lean_is_exclusive(v_i_6332_)) as u8;
                    if v_isSharedCheck_6515_ == 0 {
                        v___x_6467_ = v_i_6332_;
                        v_isShared_6468_ = v_isSharedCheck_6515_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_i_6465_);
                        lean_dec(v_i_6332_);
                        v___x_6467_ = lean_box(0);
                        v_isShared_6468_ = v_isSharedCheck_6515_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_i_6332_);
                    v___x_6516_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6;
                    v___x_6517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6517_, 0, v___x_6516_);
                    return v___x_6517_;
                }
            },
            1 => {
                v___x_6346_ = l_Lean_Expr_isSort(v_a_6342_);
                if v___x_6346_ == 0 {
                    lean_del_object(v___x_6344_);
                    lean_inc(v_a_6336_);
                    lean_inc_ref(v_a_6335_);
                    lean_inc(v_a_6334_);
                    lean_inc_ref(v_a_6333_);
                    lean_inc(v_a_6342_);
                    v___x_6347_ =
                        lean_infer_type(v_a_6342_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
                    if lean_obj_tag(v___x_6347_) == 0 {
                        v_a_6348_ = lean_ctor_get(v___x_6347_, 0);
                        lean_inc(v_a_6348_);
                        lean_dec_ref_known(v___x_6347_, 1);
                        v___x_6349_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_6348_, v_a_6334_);
                        v_a_6350_ = lean_ctor_get(v___x_6349_, 0);
                        v_isSharedCheck_6451_ = (!lean_is_exclusive(v___x_6349_)) as u8;
                        if v_isSharedCheck_6451_ == 0 {
                            v___x_6352_ = v___x_6349_;
                            v_isShared_6353_ = v_isSharedCheck_6451_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6350_);
                            lean_dec(v___x_6349_);
                            v___x_6352_ = lean_box(0);
                            v_isShared_6353_ = v_isSharedCheck_6451_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6342_);
                        v_a_6452_ = lean_ctor_get(v___x_6347_, 0);
                        v_isSharedCheck_6459_ = (!lean_is_exclusive(v___x_6347_)) as u8;
                        if v_isSharedCheck_6459_ == 0 {
                            v___x_6454_ = v___x_6347_;
                            v_isShared_6455_ = v_isSharedCheck_6459_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_6452_);
                            lean_dec(v___x_6347_);
                            v___x_6454_ = lean_box(0);
                            v_isShared_6455_ = v_isSharedCheck_6459_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6342_);
                    v___x_6460_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6;
                    if v_isShared_6345_ == 0 {
                        lean_ctor_set(v___x_6344_, 0, v___x_6460_);
                        v___x_6462_ = v___x_6344_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_6463_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6463_, 0, v___x_6460_);
                        v___x_6462_ = v_reuseFailAlloc_6463_;
                        state = 24;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6354_ =
                    l_Lean_Meta_ppExpr(v_a_6350_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
                if lean_obj_tag(v___x_6354_) == 0 {
                    if lean_obj_tag(v_a_6342_) == 4 {
                        lean_dec_ref_known(v___x_6354_, 1);
                        v_declName_6355_ = lean_ctor_get(v_a_6342_, 0);
                        lean_inc_n(v_declName_6355_, 2);
                        lean_dec_ref_known(v_a_6342_, 2);
                        v___x_6356_ = l_Lean_PrettyPrinter_ppSignature(
                            v_declName_6355_,
                            v_a_6333_,
                            v_a_6334_,
                            v_a_6335_,
                            v_a_6336_,
                        );
                        if lean_obj_tag(v___x_6356_) == 0 {
                            v_a_6357_ = lean_ctor_get(v___x_6356_, 0);
                            lean_inc(v_a_6357_);
                            lean_dec_ref_known(v___x_6356_, 1);
                            v___x_6358_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_6355_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
                            if lean_obj_tag(v___x_6358_) == 0 {
                                v_a_6359_ = lean_ctor_get(v___x_6358_, 0);
                                v_isSharedCheck_6383_ = (!lean_is_exclusive(v___x_6358_)) as u8;
                                if v_isSharedCheck_6383_ == 0 {
                                    v___x_6361_ = v___x_6358_;
                                    v_isShared_6362_ = v_isSharedCheck_6383_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6359_);
                                    lean_dec(v___x_6358_);
                                    v___x_6361_ = lean_box(0);
                                    v_isShared_6362_ = v_isSharedCheck_6383_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6357_);
                                lean_del_object(v___x_6352_);
                                v_a_6384_ = lean_ctor_get(v___x_6358_, 0);
                                v_isSharedCheck_6391_ = (!lean_is_exclusive(v___x_6358_)) as u8;
                                if v_isSharedCheck_6391_ == 0 {
                                    v___x_6386_ = v___x_6358_;
                                    v_isShared_6387_ = v_isSharedCheck_6391_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_6384_);
                                    lean_dec(v___x_6358_);
                                    v___x_6386_ = lean_box(0);
                                    v_isShared_6387_ = v_isSharedCheck_6391_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_declName_6355_);
                            lean_del_object(v___x_6352_);
                            v_a_6392_ = lean_ctor_get(v___x_6356_, 0);
                            v_isSharedCheck_6399_ = (!lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6399_ == 0 {
                                v___x_6394_ = v___x_6356_;
                                v_isShared_6395_ = v_isSharedCheck_6399_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_6392_);
                                lean_dec(v___x_6356_);
                                v___x_6394_ = lean_box(0);
                                v_isShared_6395_ = v_isSharedCheck_6399_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_6400_ = lean_ctor_get(v___x_6354_, 0);
                        lean_inc(v_a_6400_);
                        lean_dec_ref_known(v___x_6354_, 1);
                        lean_inc(v_a_6342_);
                        v___x_6401_ = l_Lean_Meta_ppExpr(
                            v_a_6342_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_,
                        );
                        if lean_obj_tag(v___x_6401_) == 0 {
                            v_a_6402_ = lean_ctor_get(v___x_6401_, 0);
                            v_isSharedCheck_6434_ = (!lean_is_exclusive(v___x_6401_)) as u8;
                            if v_isSharedCheck_6434_ == 0 {
                                v___x_6404_ = v___x_6401_;
                                v_isShared_6405_ = v_isSharedCheck_6434_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_6402_);
                                lean_dec(v___x_6401_);
                                v___x_6404_ = lean_box(0);
                                v_isShared_6405_ = v_isSharedCheck_6434_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_6400_);
                            lean_del_object(v___x_6352_);
                            lean_dec(v_a_6342_);
                            v_a_6435_ = lean_ctor_get(v___x_6401_, 0);
                            v_isSharedCheck_6442_ = (!lean_is_exclusive(v___x_6401_)) as u8;
                            if v_isSharedCheck_6442_ == 0 {
                                v___x_6437_ = v___x_6401_;
                                v_isShared_6438_ = v_isSharedCheck_6442_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_6435_);
                                lean_dec(v___x_6401_);
                                v___x_6437_ = lean_box(0);
                                v_isShared_6438_ = v_isSharedCheck_6442_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_6352_);
                    lean_dec(v_a_6342_);
                    v_a_6443_ = lean_ctor_get(v___x_6354_, 0);
                    v_isSharedCheck_6450_ = (!lean_is_exclusive(v___x_6354_)) as u8;
                    if v_isSharedCheck_6450_ == 0 {
                        v___x_6445_ = v___x_6354_;
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_6443_);
                        lean_dec(v___x_6354_);
                        v___x_6445_ = lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v_fmt_6363_ = lean_ctor_get(v_a_6357_, 0);
                v_infos_6364_ = lean_ctor_get(v_a_6357_, 1);
                v_isSharedCheck_6382_ = (!lean_is_exclusive(v_a_6357_)) as u8;
                if v_isSharedCheck_6382_ == 0 {
                    v___x_6366_ = v_a_6357_;
                    v_isShared_6367_ = v_isSharedCheck_6382_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_infos_6364_);
                    lean_inc(v_fmt_6363_);
                    lean_dec(v_a_6357_);
                    v___x_6366_ = lean_box(0);
                    v_isShared_6367_ = v_isSharedCheck_6382_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6368_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1;
                v___x_6369_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6369_, 0, v___x_6368_);
                lean_ctor_set(v___x_6369_, 1, v_fmt_6363_);
                v___x_6370_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3;
                v___x_6371_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6371_, 0, v___x_6369_);
                lean_ctor_set(v___x_6371_, 1, v___x_6370_);
                if v_isShared_6367_ == 0 {
                    lean_ctor_set(v___x_6366_, 0, v___x_6371_);
                    v___x_6373_ = v___x_6366_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6381_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6381_, 0, v___x_6371_);
                    lean_ctor_set(v_reuseFailAlloc_6381_, 1, v_infos_6364_);
                    v___x_6373_ = v_reuseFailAlloc_6381_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6353_ == 0 {
                    lean_ctor_set_tag(v___x_6352_, 1);
                    lean_ctor_set(v___x_6352_, 0, v___x_6373_);
                    v___x_6375_ = v___x_6352_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6380_, 0, v___x_6373_);
                    v___x_6375_ = v_reuseFailAlloc_6380_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6376_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6376_, 0, v___x_6375_);
                lean_ctor_set(v___x_6376_, 1, v_a_6359_);
                if v_isShared_6362_ == 0 {
                    lean_ctor_set(v___x_6361_, 0, v___x_6376_);
                    v___x_6378_ = v___x_6361_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6379_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6379_, 0, v___x_6376_);
                    v___x_6378_ = v_reuseFailAlloc_6379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6378_;
            }
            8 => {
                if v_isShared_6387_ == 0 {
                    v___x_6389_ = v___x_6386_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_a_6384_);
                    v___x_6389_ = v_reuseFailAlloc_6390_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6389_;
            }
            10 => {
                if v_isShared_6395_ == 0 {
                    v___x_6397_ = v___x_6394_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6392_);
                    v___x_6397_ = v_reuseFailAlloc_6398_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6397_;
            }
            12 => {
                if v_isDisplayableTerm_6340_ == 0 {
                    if lean_obj_tag(v_a_6342_) == 1 {
                        v_lctx_6428_ = lean_ctor_get(v_a_6333_, 2);
                        lean_inc_ref(v_lctx_6428_);
                        v___x_6429_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_6428_, v_a_6342_);
                        lean_dec_ref_known(v_a_6342_, 1);
                        if lean_obj_tag(v___x_6429_) == 1 {
                            v_val_6430_ = lean_ctor_get(v___x_6429_, 0);
                            lean_inc(v_val_6430_);
                            lean_dec_ref_known(v___x_6429_, 1);
                            v___x_6431_ = l_Lean_LocalDecl_userName(v_val_6430_);
                            lean_dec(v_val_6430_);
                            v___x_6432_ = l_Lean_Name_hasMacroScopes(v___x_6431_);
                            lean_dec(v___x_6431_);
                            if v___x_6432_ == 0 {
                                state = 16;
                                continue;
                            } else {
                                v___y_6427_ = v___x_6346_;
                                state = 17;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_6429_);
                            v___y_6427_ = v___x_6346_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6342_);
                        v___x_6433_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_6402_);
                        v___y_6427_ = v___x_6433_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6342_);
                    state = 16;
                    continue;
                }
            }
            13 => {
                v___x_6408_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1;
                v___x_6409_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6409_, 0, v___x_6408_);
                lean_ctor_set(v___x_6409_, 1, v___y_6407_);
                v___x_6410_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3;
                v___x_6411_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6411_, 0, v___x_6409_);
                lean_ctor_set(v___x_6411_, 1, v___x_6410_);
                v___x_6412_ = lean_box(1);
                v___x_6413_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6413_, 0, v___x_6411_);
                lean_ctor_set(v___x_6413_, 1, v___x_6412_);
                if v_isShared_6353_ == 0 {
                    lean_ctor_set_tag(v___x_6352_, 1);
                    lean_ctor_set(v___x_6352_, 0, v___x_6413_);
                    v___x_6415_ = v___x_6352_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6421_, 0, v___x_6413_);
                    v___x_6415_ = v_reuseFailAlloc_6421_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6416_ = lean_box(0);
                v___x_6417_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6417_, 0, v___x_6415_);
                lean_ctor_set(v___x_6417_, 1, v___x_6416_);
                if v_isShared_6405_ == 0 {
                    lean_ctor_set(v___x_6404_, 0, v___x_6417_);
                    v___x_6419_ = v___x_6404_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6420_, 0, v___x_6417_);
                    v___x_6419_ = v_reuseFailAlloc_6420_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6419_;
            }
            16 => {
                v___x_6423_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5;
                v___x_6424_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6424_, 0, v_a_6402_);
                lean_ctor_set(v___x_6424_, 1, v___x_6423_);
                v___x_6425_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6425_, 0, v___x_6424_);
                lean_ctor_set(v___x_6425_, 1, v_a_6400_);
                v___y_6407_ = v___x_6425_;
                state = 13;
                continue;
            }
            17 => {
                if v___y_6427_ == 0 {
                    lean_dec(v_a_6402_);
                    v___y_6407_ = v_a_6400_;
                    state = 13;
                    continue;
                } else {
                    state = 16;
                    continue;
                }
            }
            18 => {
                if v_isShared_6438_ == 0 {
                    v___x_6440_ = v___x_6437_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6441_, 0, v_a_6435_);
                    v___x_6440_ = v_reuseFailAlloc_6441_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6440_;
            }
            20 => {
                if v_isShared_6446_ == 0 {
                    v___x_6448_ = v___x_6445_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_a_6443_);
                    v___x_6448_ = v_reuseFailAlloc_6449_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6448_;
            }
            22 => {
                if v_isShared_6455_ == 0 {
                    v___x_6457_ = v___x_6454_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6458_, 0, v_a_6452_);
                    v___x_6457_ = v_reuseFailAlloc_6458_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6457_;
            }
            24 => {
                return v___x_6462_;
            }
            25 => {
                v_fieldName_6469_ = lean_ctor_get(v_i_6465_, 1);
                lean_inc(v_fieldName_6469_);
                v_val_6470_ = lean_ctor_get(v_i_6465_, 3);
                lean_inc_ref(v_val_6470_);
                lean_dec_ref(v_i_6465_);
                lean_inc(v_a_6336_);
                lean_inc_ref(v_a_6335_);
                lean_inc(v_a_6334_);
                lean_inc_ref(v_a_6333_);
                v___x_6471_ =
                    lean_infer_type(v_val_6470_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
                if lean_obj_tag(v___x_6471_) == 0 {
                    v_a_6472_ = lean_ctor_get(v___x_6471_, 0);
                    lean_inc(v_a_6472_);
                    lean_dec_ref_known(v___x_6471_, 1);
                    v___x_6473_ =
                        l_Lean_Meta_ppExpr(v_a_6472_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_);
                    if lean_obj_tag(v___x_6473_) == 0 {
                        v_a_6474_ = lean_ctor_get(v___x_6473_, 0);
                        v_isSharedCheck_6498_ = (!lean_is_exclusive(v___x_6473_)) as u8;
                        if v_isSharedCheck_6498_ == 0 {
                            v___x_6476_ = v___x_6473_;
                            v_isShared_6477_ = v_isSharedCheck_6498_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_6474_);
                            lean_dec(v___x_6473_);
                            v___x_6476_ = lean_box(0);
                            v_isShared_6477_ = v_isSharedCheck_6498_;
                            state = 26;
                            continue;
                        }
                    } else {
                        lean_dec(v_fieldName_6469_);
                        lean_del_object(v___x_6467_);
                        v_a_6499_ = lean_ctor_get(v___x_6473_, 0);
                        v_isSharedCheck_6506_ = (!lean_is_exclusive(v___x_6473_)) as u8;
                        if v_isSharedCheck_6506_ == 0 {
                            v___x_6501_ = v___x_6473_;
                            v_isShared_6502_ = v_isSharedCheck_6506_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_6499_);
                            lean_dec(v___x_6473_);
                            v___x_6501_ = lean_box(0);
                            v_isShared_6502_ = v_isSharedCheck_6506_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fieldName_6469_);
                    lean_del_object(v___x_6467_);
                    v_a_6507_ = lean_ctor_get(v___x_6471_, 0);
                    v_isSharedCheck_6514_ = (!lean_is_exclusive(v___x_6471_)) as u8;
                    if v_isSharedCheck_6514_ == 0 {
                        v___x_6509_ = v___x_6471_;
                        v_isShared_6510_ = v_isSharedCheck_6514_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_6507_);
                        lean_dec(v___x_6471_);
                        v___x_6509_ = lean_box(0);
                        v_isShared_6510_ = v_isSharedCheck_6514_;
                        state = 31;
                        continue;
                    }
                }
            }
            26 => {
                v___x_6478_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1;
                v___x_6479_ = 1;
                v___x_6480_ = l_Lean_Name_toString(v_fieldName_6469_, v___x_6479_);
                if v_isShared_6468_ == 0 {
                    lean_ctor_set_tag(v___x_6467_, 3);
                    lean_ctor_set(v___x_6467_, 0, v___x_6480_);
                    v___x_6482_ = v___x_6467_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6497_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6480_);
                    v___x_6482_ = v_reuseFailAlloc_6497_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_6483_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6483_, 0, v___x_6478_);
                lean_ctor_set(v___x_6483_, 1, v___x_6482_);
                v___x_6484_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5;
                v___x_6485_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6485_, 0, v___x_6483_);
                lean_ctor_set(v___x_6485_, 1, v___x_6484_);
                v___x_6486_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6486_, 0, v___x_6485_);
                lean_ctor_set(v___x_6486_, 1, v_a_6474_);
                v___x_6487_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3;
                v___x_6488_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6488_, 0, v___x_6486_);
                lean_ctor_set(v___x_6488_, 1, v___x_6487_);
                v___x_6489_ = lean_box(1);
                v___x_6490_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6490_, 0, v___x_6488_);
                lean_ctor_set(v___x_6490_, 1, v___x_6489_);
                v___x_6491_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6491_, 0, v___x_6490_);
                v___x_6492_ = lean_box(0);
                v___x_6493_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6493_, 0, v___x_6491_);
                lean_ctor_set(v___x_6493_, 1, v___x_6492_);
                if v_isShared_6477_ == 0 {
                    lean_ctor_set(v___x_6476_, 0, v___x_6493_);
                    v___x_6495_ = v___x_6476_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6496_, 0, v___x_6493_);
                    v___x_6495_ = v_reuseFailAlloc_6496_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6495_;
            }
            29 => {
                if v_isShared_6502_ == 0 {
                    v___x_6504_ = v___x_6501_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6499_);
                    v___x_6504_ = v_reuseFailAlloc_6505_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6504_;
            }
            31 => {
                if v_isShared_6510_ == 0 {
                    v___x_6512_ = v___x_6509_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
                    v___x_6512_ = v_reuseFailAlloc_6513_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(
    mut v_i_6518_: *mut LeanObject,
    mut v_a_6519_: *mut LeanObject,
    mut v_a_6520_: *mut LeanObject,
    mut v_a_6521_: *mut LeanObject,
    mut v_a_6522_: *mut LeanObject,
    mut v_a_6523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6524_: *mut LeanObject = core::ptr::null_mut();
    v_res_6524_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(
            v_i_6518_, v_a_6519_, v_a_6520_, v_a_6521_, v_a_6522_,
        );
    lean_dec(v_a_6522_);
    lean_dec_ref(v_a_6521_);
    lean_dec(v_a_6520_);
    lean_dec_ref(v_a_6519_);
    return v_res_6524_;
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f___lam__0(
    mut v_snd_6525_: *mut LeanObject,
    mut v_____r_6526_: *mut LeanObject,
    mut v_fmts_6527_: *mut LeanObject,
    mut v_infos_6528_: *mut LeanObject,
    mut v___y_6529_: *mut LeanObject,
    mut v___y_6530_: *mut LeanObject,
    mut v___y_6531_: *mut LeanObject,
    mut v___y_6532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    v___x_6534_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6534_, 0, v_fmts_6527_);
    lean_ctor_set(v___x_6534_, 1, v_infos_6528_);
    v___x_6535_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6535_, 0, v_snd_6525_);
    lean_ctor_set(v___x_6535_, 1, v___x_6534_);
    v___x_6536_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6536_, 0, v___x_6535_);
    return v___x_6536_;
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(
    mut v_snd_6537_: *mut LeanObject,
    mut v_____r_6538_: *mut LeanObject,
    mut v_fmts_6539_: *mut LeanObject,
    mut v_infos_6540_: *mut LeanObject,
    mut v___y_6541_: *mut LeanObject,
    mut v___y_6542_: *mut LeanObject,
    mut v___y_6543_: *mut LeanObject,
    mut v___y_6544_: *mut LeanObject,
    mut v___y_6545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6546_: *mut LeanObject = core::ptr::null_mut();
    v_res_6546_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(
        v_snd_6537_,
        v_____r_6538_,
        v_fmts_6539_,
        v_infos_6540_,
        v___y_6541_,
        v___y_6542_,
        v___y_6543_,
        v___y_6544_,
    );
    lean_dec(v___y_6544_);
    lean_dec_ref(v___y_6543_);
    lean_dec(v___y_6542_);
    lean_dec_ref(v___y_6541_);
    return v_res_6546_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(
    mut v_x_6547_: *mut LeanObject,
    mut v_x_6548_: *mut LeanObject,
    mut v_x_6549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6554_: u8 = 0;
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6549_) == 0 {
                    lean_dec(v_x_6547_);
                    return v_x_6548_;
                } else {
                    v_head_6550_ = lean_ctor_get(v_x_6549_, 0);
                    v_tail_6551_ = lean_ctor_get(v_x_6549_, 1);
                    v_isSharedCheck_6560_ = (!lean_is_exclusive(v_x_6549_)) as u8;
                    if v_isSharedCheck_6560_ == 0 {
                        v___x_6553_ = v_x_6549_;
                        v_isShared_6554_ = v_isSharedCheck_6560_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6551_);
                        lean_inc(v_head_6550_);
                        lean_dec(v_x_6549_);
                        v___x_6553_ = lean_box(0);
                        v_isShared_6554_ = v_isSharedCheck_6560_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6547_);
                if v_isShared_6554_ == 0 {
                    lean_ctor_set_tag(v___x_6553_, 5);
                    lean_ctor_set(v___x_6553_, 1, v_x_6547_);
                    lean_ctor_set(v___x_6553_, 0, v_x_6548_);
                    v___x_6556_ = v___x_6553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6559_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_x_6548_);
                    lean_ctor_set(v_reuseFailAlloc_6559_, 1, v_x_6547_);
                    v___x_6556_ = v_reuseFailAlloc_6559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6557_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6557_, 0, v___x_6556_);
                lean_ctor_set(v___x_6557_, 1, v_head_6550_);
                v_x_6548_ = v___x_6557_;
                v_x_6549_ = v_tail_6551_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(
    mut v_x_6561_: *mut LeanObject,
    mut v_x_6562_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6561_) == 0 {
        let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_6562_);
        v___x_6563_ = lean_box(0);
        return v___x_6563_;
    } else {
        let mut v_tail_6564_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6564_ = lean_ctor_get(v_x_6561_, 1);
        if lean_obj_tag(v_tail_6564_) == 0 {
            let mut v_head_6565_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_6562_);
            v_head_6565_ = lean_ctor_get(v_x_6561_, 0);
            lean_inc(v_head_6565_);
            lean_dec_ref_known(v_x_6561_, 2);
            return v_head_6565_;
        } else {
            let mut v_head_6566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_6564_);
            v_head_6566_ = lean_ctor_get(v_x_6561_, 0);
            lean_inc(v_head_6566_);
            lean_dec_ref_known(v_x_6561_, 2);
            v___x_6567_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_6562_, v_head_6566_, v_tail_6564_);
            return v___x_6567_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f___lam__1(
    mut v___x_6571_: *mut LeanObject,
    mut v_i_6572_: *mut LeanObject,
    mut v_fmts_6573_: *mut LeanObject,
    mut v_infos_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmts_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmts_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6610_: u8 = 0;
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6615_: u8 = 0;
    let mut v_fst_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6622_: u8 = 0;
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6626_: u8 = 0;
    let mut v___y_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6629_: u8 = 0;
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: u8 = 0;
    let mut v___x_6637_: u8 = 0;
    let mut v___y_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmt_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infos_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_i_6572_);
                v___x_6641_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_6572_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_);
                if lean_obj_tag(v___x_6641_) == 0 {
                    v_a_6642_ = lean_ctor_get(v___x_6641_, 0);
                    lean_inc(v_a_6642_);
                    lean_dec_ref_known(v___x_6641_, 1);
                    v_fst_6643_ = lean_ctor_get(v_a_6642_, 0);
                    if lean_obj_tag(v_fst_6643_) == 1 {
                        lean_dec(v_infos_6574_);
                        v_val_6644_ = lean_ctor_get(v_fst_6643_, 0);
                        lean_inc(v_val_6644_);
                        v_snd_6645_ = lean_ctor_get(v_a_6642_, 1);
                        lean_inc(v_snd_6645_);
                        lean_dec(v_a_6642_);
                        v_fmt_6646_ = lean_ctor_get(v_val_6644_, 0);
                        lean_inc(v_fmt_6646_);
                        v_infos_6647_ = lean_ctor_get(v_val_6644_, 1);
                        lean_inc(v_infos_6647_);
                        lean_dec(v_val_6644_);
                        v___x_6648_ = lean_array_push(v_fmts_6573_, v_fmt_6646_);
                        v___x_6649_ = lean_box(0);
                        v___x_6650_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(
                            v_snd_6645_,
                            v___x_6649_,
                            v___x_6648_,
                            v_infos_6647_,
                            v___y_6575_,
                            v___y_6576_,
                            v___y_6577_,
                            v___y_6578_,
                        );
                        v___y_6639_ = v___x_6650_;
                        state = 10;
                        continue;
                    } else {
                        v_snd_6651_ = lean_ctor_get(v_a_6642_, 1);
                        lean_inc(v_snd_6651_);
                        lean_dec(v_a_6642_);
                        v___x_6652_ = lean_box(0);
                        v___x_6653_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(
                            v_snd_6651_,
                            v___x_6652_,
                            v_fmts_6573_,
                            v_infos_6574_,
                            v___y_6575_,
                            v___y_6576_,
                            v___y_6577_,
                            v___y_6578_,
                        );
                        v___y_6639_ = v___x_6653_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_6654_ = lean_ctor_get(v___x_6641_, 0);
                    lean_inc(v_a_6654_);
                    lean_dec_ref_known(v___x_6641_, 1);
                    v_a_6635_ = v_a_6654_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                v___x_6583_ = lean_array_get_size(v_fmts_6582_);
                v___x_6584_ = lean_nat_dec_eq(v___x_6583_, v___x_6571_);
                if v___x_6584_ == 0 {
                    v___x_6585_ = lean_array_to_list(v_fmts_6582_);
                    v___x_6586_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1;
                    v___x_6587_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(
                        v___x_6585_,
                        v___x_6586_,
                    );
                    v___x_6588_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6588_, 0, v___x_6587_);
                    lean_ctor_set(v___x_6588_, 1, v___y_6581_);
                    v___x_6589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6589_, 0, v___x_6588_);
                    v___x_6590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6590_, 0, v___x_6589_);
                    return v___x_6590_;
                } else {
                    lean_dec_ref(v_fmts_6582_);
                    lean_dec(v___y_6581_);
                    v___x_6591_ = lean_box(0);
                    v___x_6592_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6592_, 0, v___x_6591_);
                    return v___x_6592_;
                }
            }
            2 => {
                if lean_obj_tag(v___y_6595_) == 1 {
                    v_val_6597_ = lean_ctor_get(v___y_6595_, 0);
                    lean_inc(v_val_6597_);
                    lean_dec_ref_known(v___y_6595_, 1);
                    v___x_6598_ = lean_array_push(v_fmts_6596_, v_val_6597_);
                    v___y_6581_ = v___y_6594_;
                    v_fmts_6582_ = v___x_6598_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_6595_);
                    v___y_6581_ = v___y_6594_;
                    v_fmts_6582_ = v_fmts_6596_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6601_ = l_Lean_Elab_Info_docString_x3f(
                    v_i_6572_,
                    v___y_6575_,
                    v___y_6576_,
                    v___y_6577_,
                    v___y_6578_,
                );
                if lean_obj_tag(v___x_6601_) == 0 {
                    v_snd_6602_ = lean_ctor_get(v_a_6600_, 1);
                    lean_inc(v_snd_6602_);
                    v_a_6603_ = lean_ctor_get(v___x_6601_, 0);
                    lean_inc(v_a_6603_);
                    lean_dec_ref_known(v___x_6601_, 1);
                    if lean_obj_tag(v_a_6603_) == 1 {
                        v_fst_6604_ = lean_ctor_get(v_a_6600_, 0);
                        lean_inc(v_fst_6604_);
                        lean_dec_ref(v_a_6600_);
                        v_fst_6605_ = lean_ctor_get(v_snd_6602_, 0);
                        lean_inc(v_fst_6605_);
                        v_snd_6606_ = lean_ctor_get(v_snd_6602_, 1);
                        lean_inc(v_snd_6606_);
                        lean_dec(v_snd_6602_);
                        v_val_6607_ = lean_ctor_get(v_a_6603_, 0);
                        v_isSharedCheck_6615_ = (!lean_is_exclusive(v_a_6603_)) as u8;
                        if v_isSharedCheck_6615_ == 0 {
                            v___x_6609_ = v_a_6603_;
                            v_isShared_6610_ = v_isSharedCheck_6615_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_6607_);
                            lean_dec(v_a_6603_);
                            v___x_6609_ = lean_box(0);
                            v_isShared_6610_ = v_isSharedCheck_6615_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6603_);
                        v_fst_6616_ = lean_ctor_get(v_a_6600_, 0);
                        lean_inc(v_fst_6616_);
                        lean_dec_ref(v_a_6600_);
                        v_fst_6617_ = lean_ctor_get(v_snd_6602_, 0);
                        lean_inc(v_fst_6617_);
                        v_snd_6618_ = lean_ctor_get(v_snd_6602_, 1);
                        lean_inc(v_snd_6618_);
                        lean_dec(v_snd_6602_);
                        v___y_6594_ = v_snd_6618_;
                        v___y_6595_ = v_fst_6616_;
                        v_fmts_6596_ = v_fst_6617_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_6600_);
                    v_a_6619_ = lean_ctor_get(v___x_6601_, 0);
                    v_isSharedCheck_6626_ = (!lean_is_exclusive(v___x_6601_)) as u8;
                    if v_isSharedCheck_6626_ == 0 {
                        v___x_6621_ = v___x_6601_;
                        v_isShared_6622_ = v_isSharedCheck_6626_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6619_);
                        lean_dec(v___x_6601_);
                        v___x_6621_ = lean_box(0);
                        v_isShared_6622_ = v_isSharedCheck_6626_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6610_ == 0 {
                    lean_ctor_set_tag(v___x_6609_, 3);
                    v___x_6612_ = v___x_6609_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6614_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_val_6607_);
                    v___x_6612_ = v_reuseFailAlloc_6614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6613_ = lean_array_push(v_fst_6605_, v___x_6612_);
                v___y_6594_ = v_snd_6606_;
                v___y_6595_ = v_fst_6604_;
                v_fmts_6596_ = v___x_6613_;
                state = 2;
                continue;
            }
            6 => {
                if v_isShared_6622_ == 0 {
                    v___x_6624_ = v___x_6621_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_a_6619_);
                    v___x_6624_ = v_reuseFailAlloc_6625_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6624_;
            }
            8 => {
                if v___y_6629_ == 0 {
                    lean_dec_ref(v___y_6628_);
                    v___x_6630_ = lean_box(0);
                    v___x_6631_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6631_, 0, v_fmts_6573_);
                    lean_ctor_set(v___x_6631_, 1, v_infos_6574_);
                    v___x_6632_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6632_, 0, v___x_6630_);
                    lean_ctor_set(v___x_6632_, 1, v___x_6631_);
                    v_a_6600_ = v___x_6632_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_infos_6574_);
                    lean_dec_ref(v_fmts_6573_);
                    lean_dec_ref(v_i_6572_);
                    v___x_6633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6633_, 0, v___y_6628_);
                    return v___x_6633_;
                }
            }
            9 => {
                v___x_6636_ = l_Lean_Exception_isInterrupt(v_a_6635_);
                if v___x_6636_ == 0 {
                    lean_inc_ref(v_a_6635_);
                    v___x_6637_ = l_Lean_Exception_isRuntime(v_a_6635_);
                    v___y_6628_ = v_a_6635_;
                    v___y_6629_ = v___x_6637_;
                    state = 8;
                    continue;
                } else {
                    v___y_6628_ = v_a_6635_;
                    v___y_6629_ = v___x_6636_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v_a_6640_ = lean_ctor_get(v___y_6639_, 0);
                lean_inc(v_a_6640_);
                lean_dec_ref(v___y_6639_);
                v_a_6600_ = v_a_6640_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(
    mut v___x_6655_: *mut LeanObject,
    mut v_i_6656_: *mut LeanObject,
    mut v_fmts_6657_: *mut LeanObject,
    mut v_infos_6658_: *mut LeanObject,
    mut v___y_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6664_: *mut LeanObject = core::ptr::null_mut();
    v_res_6664_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(
        v___x_6655_,
        v_i_6656_,
        v_fmts_6657_,
        v_infos_6658_,
        v___y_6659_,
        v___y_6660_,
        v___y_6661_,
        v___y_6662_,
    );
    lean_dec(v___y_6662_);
    lean_dec_ref(v___y_6661_);
    lean_dec(v___y_6660_);
    lean_dec_ref(v___y_6659_);
    lean_dec(v___x_6655_);
    return v_res_6664_;
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f(
    mut v_ci_6667_: *mut LeanObject,
    mut v_i_6668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmts_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infos_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    v___x_6670_ = l_Lean_Elab_Info_lctx(v_i_6668_);
    v___x_6671_ = lean_unsigned_to_nat(0);
    v_fmts_6672_ = l_Lean_Elab_Info_fmtHover_x3f___closed__0;
    v_infos_6673_ = lean_box(1);
    v___f_6674_ = lean_alloc_closure(
        l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_6674_, 0, v___x_6671_);
    lean_closure_set(v___f_6674_, 1, v_i_6668_);
    lean_closure_set(v___f_6674_, 2, v_fmts_6672_);
    lean_closure_set(v___f_6674_, 3, v_infos_6673_);
    v___x_6675_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_6667_, v___x_6670_, v___f_6674_);
    return v___x_6675_;
}
pub unsafe fn l_Lean_Elab_Info_fmtHover_x3f___boxed(
    mut v_ci_6676_: *mut LeanObject,
    mut v_i_6677_: *mut LeanObject,
    mut v_a_6678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6679_: *mut LeanObject = core::ptr::null_mut();
    v_res_6679_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_6676_, v_i_6677_);
    return v_res_6679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(
    mut v_hoverPos_6688_: *mut LeanObject,
    mut v_pos_6689_: *mut LeanObject,
    mut v_tailPos_6690_: *mut LeanObject,
    mut v_as_6691_: *mut LeanObject,
    mut v_i_6692_: usize,
    mut v_stop_6693_: usize,
) -> u8 {
    let mut v___x_6694_: u8 = 0;
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: u8 = 0;
    let mut v___x_6697_: usize = 0;
    let mut v___x_6698_: usize = 0;
    let mut v___x_6700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6694_ = lean_usize_dec_eq(v_i_6692_, v_stop_6693_);
                if v___x_6694_ == 0 {
                    v___x_6695_ = lean_array_uget_borrowed(v_as_6691_, v_i_6692_);
                    v___x_6696_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_6688_, v_pos_6689_, v_tailPos_6690_, v___x_6695_);
                    if v___x_6696_ == 0 {
                        v___x_6697_ = 1usize;
                        v___x_6698_ = lean_usize_add(v_i_6692_, v___x_6697_);
                        v_i_6692_ = v___x_6698_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6696_;
                    }
                } else {
                    v___x_6700_ = 0;
                    return v___x_6700_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(
    mut v_hoverPos_6701_: *mut LeanObject,
    mut v_pos_6702_: *mut LeanObject,
    mut v_tailPos_6703_: *mut LeanObject,
    mut v_x_6704_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_6704_) == 0 {
        let mut v_cs_6705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6708_: u8 = 0;
        v_cs_6705_ = lean_ctor_get(v_x_6704_, 0);
        v___x_6706_ = lean_unsigned_to_nat(0);
        v___x_6707_ = lean_array_get_size(v_cs_6705_);
        v___x_6708_ = lean_nat_dec_lt(v___x_6706_, v___x_6707_);
        if v___x_6708_ == 0 {
            return v___x_6708_;
        } else {
            if v___x_6708_ == 0 {
                return v___x_6708_;
            } else {
                let mut v___x_6709_: usize = 0;
                let mut v___x_6710_: usize = 0;
                let mut v___x_6711_: u8 = 0;
                v___x_6709_ = 0usize;
                v___x_6710_ = lean_usize_of_nat(v___x_6707_);
                v___x_6711_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_6701_, v_pos_6702_, v_tailPos_6703_, v_cs_6705_, v___x_6709_, v___x_6710_);
                return v___x_6711_;
            }
        }
    } else {
        let mut v_vs_6712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6715_: u8 = 0;
        v_vs_6712_ = lean_ctor_get(v_x_6704_, 0);
        v___x_6713_ = lean_unsigned_to_nat(0);
        v___x_6714_ = lean_array_get_size(v_vs_6712_);
        v___x_6715_ = lean_nat_dec_lt(v___x_6713_, v___x_6714_);
        if v___x_6715_ == 0 {
            return v___x_6715_;
        } else {
            if v___x_6715_ == 0 {
                return v___x_6715_;
            } else {
                let mut v___x_6716_: usize = 0;
                let mut v___x_6717_: usize = 0;
                let mut v___x_6718_: u8 = 0;
                v___x_6716_ = 0usize;
                v___x_6717_ = lean_usize_of_nat(v___x_6714_);
                v___x_6718_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_6701_, v_pos_6702_, v_tailPos_6703_, v_vs_6712_, v___x_6716_, v___x_6717_);
                return v___x_6718_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(
    mut v_hoverPos_6719_: *mut LeanObject,
    mut v_pos_6720_: *mut LeanObject,
    mut v_tailPos_6721_: *mut LeanObject,
    mut v_t_6722_: *mut LeanObject,
) -> u8 {
    let mut v_root_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: u8 = 0;
    v_root_6723_ = lean_ctor_get(v_t_6722_, 0);
    v_tail_6724_ = lean_ctor_get(v_t_6722_, 1);
    v___x_6725_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_6719_, v_pos_6720_, v_tailPos_6721_, v_root_6723_);
    if v___x_6725_ == 0 {
        let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6728_: u8 = 0;
        v___x_6726_ = lean_unsigned_to_nat(0);
        v___x_6727_ = lean_array_get_size(v_tail_6724_);
        v___x_6728_ = lean_nat_dec_lt(v___x_6726_, v___x_6727_);
        if v___x_6728_ == 0 {
            return v___x_6725_;
        } else {
            if v___x_6728_ == 0 {
                return v___x_6725_;
            } else {
                let mut v___x_6729_: usize = 0;
                let mut v___x_6730_: usize = 0;
                let mut v___x_6731_: u8 = 0;
                v___x_6729_ = 0usize;
                v___x_6730_ = lean_usize_of_nat(v___x_6727_);
                v___x_6731_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_6719_, v_pos_6720_, v_tailPos_6721_, v_tail_6724_, v___x_6729_, v___x_6730_);
                return v___x_6731_;
            }
        }
    } else {
        return v___x_6725_;
    }
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(
    mut v_hoverPos_6732_: *mut LeanObject,
    mut v_pos_6733_: *mut LeanObject,
    mut v_tailPos_6734_: *mut LeanObject,
    mut v_a_6735_: *mut LeanObject,
) -> u8 {
    let mut v_i_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: u8 = 0;
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: u8 = 0;
    let mut v___y_6747_: u8 = 0;
    let mut v___x_6748_: u8 = 0;
    let mut v___x_6749_: u8 = 0;
    let mut v___y_6751_: u8 = 0;
    let mut v___x_6752_: u8 = 0;
    let mut v___x_6753_: u8 = 0;
    let mut v___x_6754_: u8 = 0;
    let mut v___x_6755_: u8 = 0;
    let mut v___x_6756_: u8 = 0;
    let mut v_children_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: u8 = 0;
    let mut v___x_6759_: u8 = 0;
    let mut v___x_6760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6735_) == 1 {
                    v_i_6736_ = lean_ctor_get(v_a_6735_, 0);
                    match lean_obj_tag(v_i_6736_) {
                        0 => {
                            v_children_6737_ = lean_ctor_get(v_a_6735_, 1);
                            v___x_6738_ = l_Lean_Elab_Info_stx(v_i_6736_);
                            v___x_6739_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3;
                            v___x_6740_ = l_Lean_Syntax_isOfKind(v___x_6738_, v___x_6739_);
                            if v___x_6740_ == 0 {
                                v___x_6741_ = l_Lean_Elab_Info_pos_x3f(v_i_6736_);
                                if lean_obj_tag(v___x_6741_) == 1 {
                                    v_val_6742_ = lean_ctor_get(v___x_6741_, 0);
                                    lean_inc(v_val_6742_);
                                    lean_dec_ref_known(v___x_6741_, 1);
                                    v___x_6743_ = l_Lean_Elab_Info_tailPos_x3f(v_i_6736_);
                                    if lean_obj_tag(v___x_6743_) == 1 {
                                        v_val_6744_ = lean_ctor_get(v___x_6743_, 0);
                                        lean_inc(v_val_6744_);
                                        lean_dec_ref_known(v___x_6743_, 1);
                                        v___x_6745_ = 1;
                                        v___x_6749_ =
                                            lean_nat_dec_lt(v_hoverPos_6732_, v_val_6744_);
                                        if v___x_6749_ == 0 {
                                            lean_dec(v_val_6744_);
                                            lean_dec(v_val_6742_);
                                            v___y_6747_ = v___x_6749_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_6752_ = lean_nat_dec_eq(v_val_6742_, v_pos_6733_);
                                            lean_dec(v_val_6742_);
                                            if v___x_6752_ == 0 {
                                                lean_dec(v_val_6744_);
                                                v___y_6751_ = v___x_6752_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_6753_ =
                                                    lean_nat_dec_eq(v_val_6744_, v_tailPos_6734_);
                                                lean_dec(v_val_6744_);
                                                v___y_6751_ = v___x_6753_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_6743_);
                                        lean_dec(v_val_6742_);
                                        v___x_6754_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6732_, v_pos_6733_, v_tailPos_6734_, v_children_6737_);
                                        return v___x_6754_;
                                    }
                                } else {
                                    lean_dec(v___x_6741_);
                                    v___x_6755_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6732_, v_pos_6733_, v_tailPos_6734_, v_children_6737_);
                                    return v___x_6755_;
                                }
                            } else {
                                v___x_6756_ = 0;
                                return v___x_6756_;
                            }
                        }
                        4 => {
                            v_children_6757_ = lean_ctor_get(v_a_6735_, 1);
                            v___x_6758_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6732_, v_pos_6733_, v_tailPos_6734_, v_children_6757_);
                            return v___x_6758_;
                        }
                        _ => {
                            v___x_6759_ = 0;
                            return v___x_6759_;
                        }
                    }
                } else {
                    v___x_6760_ = 0;
                    return v___x_6760_;
                }
            }
            1 => {
                if v___y_6747_ == 0 {
                    v___x_6748_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6732_, v_pos_6733_, v_tailPos_6734_, v_children_6737_);
                    return v___x_6748_;
                } else {
                    return v___x_6745_;
                }
            }
            2 => {
                if v___y_6751_ == 0 {
                    v___y_6747_ = v___x_6749_;
                    state = 1;
                    continue;
                } else {
                    v___y_6747_ = v___x_6740_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(
    mut v_hoverPos_6761_: *mut LeanObject,
    mut v_pos_6762_: *mut LeanObject,
    mut v_tailPos_6763_: *mut LeanObject,
    mut v_as_6764_: *mut LeanObject,
    mut v_i_6765_: usize,
    mut v_stop_6766_: usize,
) -> u8 {
    let mut v___x_6767_: u8 = 0;
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6770_: usize = 0;
    let mut v___x_6771_: usize = 0;
    let mut v___x_6773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6767_ = lean_usize_dec_eq(v_i_6765_, v_stop_6766_);
                if v___x_6767_ == 0 {
                    v___x_6768_ = lean_array_uget_borrowed(v_as_6764_, v_i_6765_);
                    v___x_6769_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_6761_, v_pos_6762_, v_tailPos_6763_, v___x_6768_);
                    if v___x_6769_ == 0 {
                        v___x_6770_ = 1usize;
                        v___x_6771_ = lean_usize_add(v_i_6765_, v___x_6770_);
                        v_i_6765_ = v___x_6771_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6769_;
                    }
                } else {
                    v___x_6773_ = 0;
                    return v___x_6773_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(
    mut v_hoverPos_6774_: *mut LeanObject,
    mut v_pos_6775_: *mut LeanObject,
    mut v_tailPos_6776_: *mut LeanObject,
    mut v_as_6777_: *mut LeanObject,
    mut v_i_6778_: *mut LeanObject,
    mut v_stop_6779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6780_: usize = 0;
    let mut v_stop_boxed_6781_: usize = 0;
    let mut v_res_6782_: u8 = 0;
    let mut v_r_6783_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6780_ = lean_unbox_usize(v_i_6778_);
    lean_dec(v_i_6778_);
    v_stop_boxed_6781_ = lean_unbox_usize(v_stop_6779_);
    lean_dec(v_stop_6779_);
    v_res_6782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_6774_, v_pos_6775_, v_tailPos_6776_, v_as_6777_, v_i_boxed_6780_, v_stop_boxed_6781_);
    lean_dec_ref(v_as_6777_);
    lean_dec(v_tailPos_6776_);
    lean_dec(v_pos_6775_);
    lean_dec(v_hoverPos_6774_);
    v_r_6783_ = lean_box((v_res_6782_) as usize);
    return v_r_6783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(
    mut v_hoverPos_6784_: *mut LeanObject,
    mut v_pos_6785_: *mut LeanObject,
    mut v_tailPos_6786_: *mut LeanObject,
    mut v_as_6787_: *mut LeanObject,
    mut v_i_6788_: *mut LeanObject,
    mut v_stop_6789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6790_: usize = 0;
    let mut v_stop_boxed_6791_: usize = 0;
    let mut v_res_6792_: u8 = 0;
    let mut v_r_6793_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6790_ = lean_unbox_usize(v_i_6788_);
    lean_dec(v_i_6788_);
    v_stop_boxed_6791_ = lean_unbox_usize(v_stop_6789_);
    lean_dec(v_stop_6789_);
    v_res_6792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_6784_, v_pos_6785_, v_tailPos_6786_, v_as_6787_, v_i_boxed_6790_, v_stop_boxed_6791_);
    lean_dec_ref(v_as_6787_);
    lean_dec(v_tailPos_6786_);
    lean_dec(v_pos_6785_);
    lean_dec(v_hoverPos_6784_);
    v_r_6793_ = lean_box((v_res_6792_) as usize);
    return v_r_6793_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(
    mut v_hoverPos_6794_: *mut LeanObject,
    mut v_pos_6795_: *mut LeanObject,
    mut v_tailPos_6796_: *mut LeanObject,
    mut v_t_6797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6798_: u8 = 0;
    let mut v_r_6799_: *mut LeanObject = core::ptr::null_mut();
    v_res_6798_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6794_, v_pos_6795_, v_tailPos_6796_, v_t_6797_);
    lean_dec_ref(v_t_6797_);
    lean_dec(v_tailPos_6796_);
    lean_dec(v_pos_6795_);
    lean_dec(v_hoverPos_6794_);
    v_r_6799_ = lean_box((v_res_6798_) as usize);
    return v_r_6799_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(
    mut v_hoverPos_6800_: *mut LeanObject,
    mut v_pos_6801_: *mut LeanObject,
    mut v_tailPos_6802_: *mut LeanObject,
    mut v_x_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6804_: u8 = 0;
    let mut v_r_6805_: *mut LeanObject = core::ptr::null_mut();
    v_res_6804_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_6800_, v_pos_6801_, v_tailPos_6802_, v_x_6803_);
    lean_dec_ref(v_x_6803_);
    lean_dec(v_tailPos_6802_);
    lean_dec(v_pos_6801_);
    lean_dec(v_hoverPos_6800_);
    v_r_6805_ = lean_box((v_res_6804_) as usize);
    return v_r_6805_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(
    mut v_hoverPos_6806_: *mut LeanObject,
    mut v_pos_6807_: *mut LeanObject,
    mut v_tailPos_6808_: *mut LeanObject,
    mut v_a_6809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6810_: u8 = 0;
    let mut v_r_6811_: *mut LeanObject = core::ptr::null_mut();
    v_res_6810_ =
        l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(
            v_hoverPos_6806_,
            v_pos_6807_,
            v_tailPos_6808_,
            v_a_6809_,
        );
    lean_dec_ref(v_a_6809_);
    lean_dec(v_tailPos_6808_);
    lean_dec(v_pos_6807_);
    lean_dec(v_hoverPos_6806_);
    v_r_6811_ = lean_box((v_res_6810_) as usize);
    return v_r_6811_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(
    mut v_x_6812_: *mut LeanObject,
    mut v_x_6813_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_6812_) == 0 {
        if lean_obj_tag(v_x_6813_) == 0 {
            let mut v___x_6814_: u8 = 0;
            v___x_6814_ = 1;
            return v___x_6814_;
        } else {
            let mut v___x_6815_: u8 = 0;
            v___x_6815_ = 0;
            return v___x_6815_;
        }
    } else {
        if lean_obj_tag(v_x_6813_) == 0 {
            let mut v___x_6816_: u8 = 0;
            v___x_6816_ = 0;
            return v___x_6816_;
        } else {
            let mut v_val_6817_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_6818_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6819_: u8 = 0;
            v_val_6817_ = lean_ctor_get(v_x_6812_, 0);
            v_val_6818_ = lean_ctor_get(v_x_6813_, 0);
            v___x_6819_ = lean_nat_dec_eq(v_val_6817_, v_val_6818_);
            return v___x_6819_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(
    mut v_x_6820_: *mut LeanObject,
    mut v_x_6821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6822_: u8 = 0;
    let mut v_r_6823_: *mut LeanObject = core::ptr::null_mut();
    v_res_6822_ =
        l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_6820_, v_x_6821_);
    lean_dec(v_x_6821_);
    lean_dec(v_x_6820_);
    v_r_6823_ = lean_box((v_res_6822_) as usize);
    return v_r_6823_;
}
pub unsafe fn l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(
    mut v_x_6824_: *mut LeanObject,
) -> u8 {
    let mut v___x_6825_: u8 = 0;
    let mut v_head_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indented_6827_: u8 = 0;
    let mut v_tail_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6824_) == 0 {
                    v___x_6825_ = 1;
                    return v___x_6825_;
                } else {
                    v_head_6826_ = lean_ctor_get(v_x_6824_, 0);
                    v_indented_6827_ = lean_ctor_get_uint8(
                        v_head_6826_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    if v_indented_6827_ == 0 {
                        return v_indented_6827_;
                    } else {
                        v_tail_6828_ = lean_ctor_get(v_x_6824_, 1);
                        v_x_6824_ = v_tail_6828_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(
    mut v_x_6830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6831_: u8 = 0;
    let mut v_r_6832_: *mut LeanObject = core::ptr::null_mut();
    v_res_6831_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_x_6830_);
    lean_dec(v_x_6830_);
    v_r_6832_ = lean_box((v_res_6831_) as usize);
    return v_r_6832_;
}
pub unsafe fn l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(
    mut v_text_6833_: *mut LeanObject,
    mut v_hoverPos_6834_: *mut LeanObject,
    mut v_ctx_6835_: *mut LeanObject,
    mut v_i_6836_: *mut LeanObject,
    mut v_cs_6837_: *mut LeanObject,
    mut v_gs_6838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6841_: u8 = 0;
    let mut v___y_6842_: u8 = 0;
    let mut v___y_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trailSize_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6857_: u8 = 0;
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: u8 = 0;
    let mut v___x_6863_: u8 = 0;
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6867_: u8 = 0;
    let mut v___x_6868_: u8 = 0;
    let mut v___x_6869_: u8 = 0;
    let mut v___x_6870_: u8 = 0;
    let mut v___y_6872_: u8 = 0;
    let mut v___x_6873_: u8 = 0;
    let mut v___x_6874_: u8 = 0;
    let mut v___x_6875_: u8 = 0;
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_atEOF_6877_: u8 = 0;
    let mut v___y_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: u8 = 0;
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_i_6836_) == 0 {
                    v_i_6839_ = lean_ctor_get(v_i_6836_, 0);
                    v___x_6847_ = l_Lean_Elab_Info_pos_x3f(v_i_6836_);
                    if lean_obj_tag(v___x_6847_) == 1 {
                        v_val_6848_ = lean_ctor_get(v___x_6847_, 0);
                        lean_inc(v_val_6848_);
                        lean_dec_ref_known(v___x_6847_, 1);
                        v___x_6849_ = l_Lean_Elab_Info_tailPos_x3f(v_i_6836_);
                        if lean_obj_tag(v___x_6849_) == 1 {
                            v_val_6850_ = lean_ctor_get(v___x_6849_, 0);
                            lean_inc(v_val_6850_);
                            lean_dec_ref_known(v___x_6849_, 1);
                            v_source_6851_ = lean_ctor_get(v_text_6833_, 0);
                            v___x_6852_ = lean_nat_dec_le(v_val_6848_, v_hoverPos_6834_);
                            if v___x_6852_ == 0 {
                                lean_dec(v_val_6850_);
                                lean_dec(v_val_6848_);
                                lean_dec_ref(v_ctx_6835_);
                                lean_dec_ref(v_text_6833_);
                                lean_inc(v_gs_6838_);
                                return v_gs_6838_;
                            } else {
                                v___x_6853_ = l_Lean_Elab_Info_stx(v_i_6836_);
                                v_trailSize_6854_ = l_Lean_Syntax_getTrailingSize(v___x_6853_);
                                lean_dec(v___x_6853_);
                                v___x_6855_ = lean_nat_add(v_val_6850_, v_trailSize_6854_);
                                v___x_6876_ = lean_string_utf8_byte_size(v_source_6851_);
                                v_atEOF_6877_ = lean_nat_dec_eq(v___x_6855_, v___x_6876_);
                                v___x_6882_ = lean_unsigned_to_nat(1);
                                v___x_6883_ = lean_nat_dec_le(v___x_6882_, v_trailSize_6854_);
                                if v___x_6883_ == 0 {
                                    lean_dec(v_trailSize_6854_);
                                    v___y_6879_ = v___x_6882_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___y_6879_ = v_trailSize_6854_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_6849_);
                            lean_dec(v_val_6848_);
                            lean_dec_ref(v_ctx_6835_);
                            lean_dec_ref(v_text_6833_);
                            lean_inc(v_gs_6838_);
                            return v_gs_6838_;
                        }
                    } else {
                        lean_dec(v___x_6847_);
                        lean_dec_ref(v_ctx_6835_);
                        lean_dec_ref(v_text_6833_);
                        lean_inc(v_gs_6838_);
                        return v_gs_6838_;
                    }
                } else {
                    lean_dec_ref(v_ctx_6835_);
                    lean_dec_ref(v_text_6833_);
                    lean_inc(v_gs_6838_);
                    return v_gs_6838_;
                }
            }
            1 => {
                lean_inc_ref(v_i_6839_);
                v___x_6844_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_6844_, 0, v_ctx_6835_);
                lean_ctor_set(v___x_6844_, 1, v_i_6839_);
                lean_ctor_set(v___x_6844_, 2, v___y_6843_);
                lean_ctor_set_uint8(
                    v___x_6844_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_6841_,
                );
                lean_ctor_set_uint8(
                    v___x_6844_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___y_6842_,
                );
                v___x_6845_ = lean_box(0);
                v___x_6846_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6846_, 0, v___x_6844_);
                lean_ctor_set(v___x_6846_, 1, v___x_6845_);
                return v___x_6846_;
            }
            2 => {
                lean_inc_ref(v_text_6833_);
                v___x_6858_ = l_Lean_FileMap_toPosition(v_text_6833_, v_hoverPos_6834_);
                v_column_6859_ = lean_ctor_get(v___x_6858_, 1);
                lean_inc(v_column_6859_);
                lean_dec_ref(v___x_6858_);
                v___x_6860_ = l_Lean_FileMap_toPosition(v_text_6833_, v_val_6848_);
                lean_dec(v_val_6848_);
                v_column_6861_ = lean_ctor_get(v___x_6860_, 1);
                lean_inc(v_column_6861_);
                lean_dec_ref(v___x_6860_);
                v___x_6862_ = lean_nat_dec_lt(v_column_6859_, v_column_6861_);
                lean_dec(v_column_6861_);
                lean_dec(v_column_6859_);
                v___x_6863_ = lean_nat_dec_eq(v_hoverPos_6834_, v___x_6855_);
                lean_dec(v___x_6855_);
                if v___x_6863_ == 0 {
                    v___x_6864_ = lean_unsigned_to_nat(1);
                    v___y_6841_ = v___y_6857_;
                    v___y_6842_ = v___x_6862_;
                    v___y_6843_ = v___x_6864_;
                    state = 1;
                    continue;
                } else {
                    v___x_6865_ = lean_unsigned_to_nat(0);
                    v___y_6841_ = v___y_6857_;
                    v___y_6842_ = v___x_6862_;
                    v___y_6843_ = v___x_6865_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_6867_ == 0 {
                    lean_dec(v___x_6855_);
                    lean_dec(v_val_6850_);
                    lean_dec(v_val_6848_);
                    lean_dec_ref(v_ctx_6835_);
                    lean_dec_ref(v_text_6833_);
                    lean_inc(v_gs_6838_);
                    return v_gs_6838_;
                } else {
                    v___x_6868_ = lean_nat_dec_lt(v_val_6848_, v_hoverPos_6834_);
                    if v___x_6868_ == 0 {
                        lean_dec(v_val_6850_);
                        v___y_6857_ = v___x_6868_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6869_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_6834_, v_val_6848_, v_val_6850_, v_cs_6837_);
                        lean_dec(v_val_6850_);
                        if v___x_6869_ == 0 {
                            v___y_6857_ = v___x_6868_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6870_ = 0;
                            v___y_6857_ = v___x_6870_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___y_6872_ == 0 {
                    lean_dec(v___x_6855_);
                    lean_dec(v_val_6850_);
                    lean_dec(v_val_6848_);
                    lean_dec_ref(v_ctx_6835_);
                    lean_dec_ref(v_text_6833_);
                    lean_inc(v_gs_6838_);
                    return v_gs_6838_;
                } else {
                    v___x_6873_ = l_List_isEmpty___redArg(v_gs_6838_);
                    if v___x_6873_ == 0 {
                        v___x_6874_ = lean_nat_dec_le(v_val_6850_, v_hoverPos_6834_);
                        if v___x_6874_ == 0 {
                            v___y_6867_ = v___x_6874_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6875_ =
                                l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(
                                    v_gs_6838_,
                                );
                            v___y_6867_ = v___x_6875_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_6867_ = v___x_6873_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6880_ = lean_nat_add(v_val_6850_, v___y_6879_);
                lean_dec(v___y_6879_);
                v___x_6881_ = lean_nat_dec_lt(v_hoverPos_6834_, v___x_6880_);
                lean_dec(v___x_6880_);
                if v___x_6881_ == 0 {
                    v___y_6872_ = v_atEOF_6877_;
                    state = 4;
                    continue;
                } else {
                    v___y_6872_ = v___x_6881_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(
    mut v_text_6884_: *mut LeanObject,
    mut v_hoverPos_6885_: *mut LeanObject,
    mut v_ctx_6886_: *mut LeanObject,
    mut v_i_6887_: *mut LeanObject,
    mut v_cs_6888_: *mut LeanObject,
    mut v_gs_6889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6890_: *mut LeanObject = core::ptr::null_mut();
    v_res_6890_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(
        v_text_6884_,
        v_hoverPos_6885_,
        v_ctx_6886_,
        v_i_6887_,
        v_cs_6888_,
        v_gs_6889_,
    );
    lean_dec(v_gs_6889_);
    lean_dec_ref(v_cs_6888_);
    lean_dec_ref(v_i_6887_);
    lean_dec(v_hoverPos_6885_);
    return v_res_6890_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(
    mut v_a_6891_: *mut LeanObject,
    mut v_a_6892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v_priority_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6891_) == 0 {
                    v___x_6893_ = l_List_reverse___redArg(v_a_6892_);
                    return v___x_6893_;
                } else {
                    v_head_6894_ = lean_ctor_get(v_a_6891_, 0);
                    v_tail_6895_ = lean_ctor_get(v_a_6891_, 1);
                    v_isSharedCheck_6904_ = (!lean_is_exclusive(v_a_6891_)) as u8;
                    if v_isSharedCheck_6904_ == 0 {
                        v___x_6897_ = v_a_6891_;
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6895_);
                        lean_inc(v_head_6894_);
                        lean_dec(v_a_6891_);
                        v___x_6897_ = lean_box(0);
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_priority_6899_ = lean_ctor_get(v_head_6894_, 2);
                lean_inc(v_priority_6899_);
                lean_dec(v_head_6894_);
                if v_isShared_6898_ == 0 {
                    lean_ctor_set(v___x_6897_, 1, v_a_6892_);
                    lean_ctor_set(v___x_6897_, 0, v_priority_6899_);
                    v___x_6901_ = v___x_6897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6903_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_priority_6899_);
                    lean_ctor_set(v_reuseFailAlloc_6903_, 1, v_a_6892_);
                    v___x_6901_ = v_reuseFailAlloc_6903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6891_ = v_tail_6895_;
                v_a_6892_ = v___x_6901_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(
    mut v_maxPrio_x3f_6905_: *mut LeanObject,
    mut v_a_6906_: *mut LeanObject,
    mut v_a_6907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6913_: u8 = 0;
    let mut v_priority_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: u8 = 0;
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6906_) == 0 {
                    v___x_6908_ = l_List_reverse___redArg(v_a_6907_);
                    return v___x_6908_;
                } else {
                    v_head_6909_ = lean_ctor_get(v_a_6906_, 0);
                    v_tail_6910_ = lean_ctor_get(v_a_6906_, 1);
                    v_isSharedCheck_6922_ = (!lean_is_exclusive(v_a_6906_)) as u8;
                    if v_isSharedCheck_6922_ == 0 {
                        v___x_6912_ = v_a_6906_;
                        v_isShared_6913_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6910_);
                        lean_inc(v_head_6909_);
                        lean_dec(v_a_6906_);
                        v___x_6912_ = lean_box(0);
                        v_isShared_6913_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_priority_6914_ = lean_ctor_get(v_head_6909_, 2);
                lean_inc(v_priority_6914_);
                v___x_6915_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6915_, 0, v_priority_6914_);
                v___x_6916_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(
                    v___x_6915_,
                    v_maxPrio_x3f_6905_,
                );
                lean_dec_ref_known(v___x_6915_, 1);
                if v___x_6916_ == 0 {
                    lean_del_object(v___x_6912_);
                    lean_dec(v_head_6909_);
                    v_a_6906_ = v_tail_6910_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_6913_ == 0 {
                        lean_ctor_set(v___x_6912_, 1, v_a_6907_);
                        v___x_6919_ = v___x_6912_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6921_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6921_, 0, v_head_6909_);
                        lean_ctor_set(v_reuseFailAlloc_6921_, 1, v_a_6907_);
                        v___x_6919_ = v_reuseFailAlloc_6921_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6906_ = v_tail_6910_;
                v_a_6907_ = v___x_6919_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(
    mut v_maxPrio_x3f_6923_: *mut LeanObject,
    mut v_a_6924_: *mut LeanObject,
    mut v_a_6925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6926_: *mut LeanObject = core::ptr::null_mut();
    v_res_6926_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(
        v_maxPrio_x3f_6923_,
        v_a_6924_,
        v_a_6925_,
    );
    lean_dec(v_maxPrio_x3f_6923_);
    return v_res_6926_;
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(
    mut v_x_6927_: *mut LeanObject,
    mut v_x_6928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6928_) == 0 {
                    lean_inc(v_x_6927_);
                    return v_x_6927_;
                } else {
                    v_head_6929_ = lean_ctor_get(v_x_6928_, 0);
                    v_tail_6930_ = lean_ctor_get(v_x_6928_, 1);
                    v___x_6931_ = lean_nat_dec_le(v_x_6927_, v_head_6929_);
                    if v___x_6931_ == 0 {
                        v_x_6928_ = v_tail_6930_;
                        state = 0;
                        continue;
                    } else {
                        v_x_6927_ = v_head_6929_;
                        v_x_6928_ = v_tail_6930_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2___boxed(
    mut v_x_6934_: *mut LeanObject,
    mut v_x_6935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6936_: *mut LeanObject = core::ptr::null_mut();
    v_res_6936_ =
        l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(
            v_x_6934_, v_x_6935_,
        );
    lean_dec(v_x_6935_);
    lean_dec(v_x_6934_);
    return v_res_6936_;
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(
    mut v_x_6937_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6937_) == 0 {
        let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
        v___x_6938_ = lean_box(0);
        return v___x_6938_;
    } else {
        let mut v_head_6939_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_6940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6942_: *mut LeanObject = core::ptr::null_mut();
        v_head_6939_ = lean_ctor_get(v_x_6937_, 0);
        v_tail_6940_ = lean_ctor_get(v_x_6937_, 1);
        v___x_6941_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(v_head_6939_, v_tail_6940_);
        v___x_6942_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6942_, 0, v___x_6941_);
        return v___x_6942_;
    }
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2___boxed(
    mut v_x_6943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6944_: *mut LeanObject = core::ptr::null_mut();
    v_res_6944_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_x_6943_);
    lean_dec(v_x_6943_);
    return v_res_6944_;
}
pub unsafe fn l_Lean_Elab_InfoTree_goalsAt_x3f(
    mut v_text_6945_: *mut LeanObject,
    mut v_t_6946_: *mut LeanObject,
    mut v_hoverPos_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gs_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxPrio_x3f_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    v___f_6948_ = lean_alloc_closure(
        l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_6948_, 0, v_text_6945_);
    lean_closure_set(v___f_6948_, 1, v_hoverPos_6947_);
    v_gs_6949_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_6948_, v_t_6946_);
    v___x_6950_ = lean_box(0);
    lean_inc(v_gs_6949_);
    v___x_6951_ =
        l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_6949_, v___x_6950_);
    v_maxPrio_x3f_6952_ =
        l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v___x_6951_);
    lean_dec(v___x_6951_);
    v___x_6953_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(
        v_maxPrio_x3f_6952_,
        v_gs_6949_,
        v___x_6950_,
    );
    lean_dec(v_maxPrio_x3f_6952_);
    return v___x_6953_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(
    mut v___x_6954_: *mut LeanObject,
    mut v___y_6955_: u8,
    mut v_a_6956_: *mut LeanObject,
    mut v_a_6957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6964_: u8 = 0;
    let mut v_info_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6976_: u8 = 0;
    let mut v_unused_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6956_) == 0 {
                    v___x_6958_ = l_List_reverse___redArg(v_a_6957_);
                    return v___x_6958_;
                } else {
                    v_head_6959_ = lean_ctor_get(v_a_6956_, 0);
                    lean_inc(v_head_6959_);
                    v_snd_6960_ = lean_ctor_get(v_head_6959_, 1);
                    v_tail_6961_ = lean_ctor_get(v_a_6956_, 1);
                    v_isSharedCheck_6976_ = (!lean_is_exclusive(v_a_6956_)) as u8;
                    if v_isSharedCheck_6976_ == 0 {
                        v_unused_6977_ = lean_ctor_get(v_a_6956_, 0);
                        lean_dec(v_unused_6977_);
                        v___x_6963_ = v_a_6956_;
                        v_isShared_6964_ = v_isSharedCheck_6976_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6961_);
                        lean_dec(v_a_6956_);
                        v___x_6963_ = lean_box(0);
                        v_isShared_6964_ = v_isSharedCheck_6976_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_info_6965_ = lean_ctor_get(v_snd_6960_, 1);
                v___x_6966_ = l_Lean_Elab_Info_stx(v_info_6965_);
                v___x_6967_ = lean_unsigned_to_nat(0);
                v___x_6968_ = l_Lean_Syntax_getArg(v___x_6954_, v___x_6967_);
                v___x_6969_ = l_Lean_Syntax_structEq(v___x_6966_, v___x_6968_);
                if v___x_6969_ == 0 {
                    if v___y_6955_ == 0 {
                        lean_del_object(v___x_6963_);
                        lean_dec(v_head_6959_);
                        v_a_6956_ = v_tail_6961_;
                        state = 0;
                        continue;
                    } else {
                        if v_isShared_6964_ == 0 {
                            lean_ctor_set(v___x_6963_, 1, v_a_6957_);
                            v___x_6972_ = v___x_6963_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6974_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6974_, 0, v_head_6959_);
                            lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_a_6957_);
                            v___x_6972_ = v_reuseFailAlloc_6974_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6963_);
                    lean_dec(v_head_6959_);
                    v_a_6956_ = v_tail_6961_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_6956_ = v_tail_6961_;
                v_a_6957_ = v___x_6972_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(
    mut v___x_6978_: *mut LeanObject,
    mut v___y_6979_: *mut LeanObject,
    mut v_a_6980_: *mut LeanObject,
    mut v_a_6981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1121__boxed_6982_: u8 = 0;
    let mut v_res_6983_: *mut LeanObject = core::ptr::null_mut();
    v___y_1121__boxed_6982_ = (lean_unbox(v___y_6979_) as u8);
    v_res_6983_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(
        v___x_6978_,
        v___y_1121__boxed_6982_,
        v_a_6980_,
        v_a_6981_,
    );
    lean_dec(v___x_6978_);
    return v_res_6983_;
}
pub unsafe fn l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(
    mut v_ctx_6990_: *mut LeanObject,
    mut v_info_6991_: *mut LeanObject,
    mut v_children_6992_: *mut LeanObject,
    mut v_results_6993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6996_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: u8 = 0;
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6994_ = l_Lean_Elab_Info_stx(v_info_6991_);
                v___x_6999_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1;
                lean_inc(v___x_6994_);
                v___x_7000_ = l_Lean_Syntax_isOfKind(v___x_6994_, v___x_6999_);
                if v___x_7000_ == 0 {
                    v___y_6996_ = v___x_7000_;
                    state = 1;
                    continue;
                } else {
                    v___x_7001_ = lean_unsigned_to_nat(0);
                    v___x_7002_ = l_Lean_Syntax_getArg(v___x_6994_, v___x_7001_);
                    v___x_7003_ = l_Lean_Syntax_isIdent(v___x_7002_);
                    lean_dec(v___x_7002_);
                    v___y_6996_ = v___x_7003_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_6996_ == 0 {
                    lean_dec(v___x_6994_);
                    return v_results_6993_;
                } else {
                    v___x_6997_ = lean_box(0);
                    v___x_6998_ =
                        l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(
                            v___x_6994_,
                            v___y_6996_,
                            v_results_6993_,
                            v___x_6997_,
                        );
                    lean_dec(v___x_6994_);
                    return v___x_6998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(
    mut v_ctx_7004_: *mut LeanObject,
    mut v_info_7005_: *mut LeanObject,
    mut v_children_7006_: *mut LeanObject,
    mut v_results_7007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7008_: *mut LeanObject = core::ptr::null_mut();
    v_res_7008_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(
        v_ctx_7004_,
        v_info_7005_,
        v_children_7006_,
        v_results_7007_,
    );
    lean_dec_ref(v_children_7006_);
    lean_dec_ref(v_info_7005_);
    lean_dec_ref(v_ctx_7004_);
    return v_res_7008_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(
    mut v_x_7009_: *mut LeanObject,
    mut v_x_7010_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_7009_) == 0 {
        if lean_obj_tag(v_x_7010_) == 0 {
            let mut v___x_7011_: u8 = 0;
            v___x_7011_ = 1;
            return v___x_7011_;
        } else {
            let mut v___x_7012_: u8 = 0;
            v___x_7012_ = 0;
            return v___x_7012_;
        }
    } else {
        if lean_obj_tag(v_x_7010_) == 0 {
            let mut v___x_7013_: u8 = 0;
            v___x_7013_ = 0;
            return v___x_7013_;
        } else {
            let mut v_val_7014_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_7015_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7016_: u8 = 0;
            v_val_7014_ = lean_ctor_get(v_x_7009_, 0);
            v_val_7015_ = lean_ctor_get(v_x_7010_, 0);
            v___x_7016_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_7014_, v_val_7015_);
            return v___x_7016_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(
    mut v_x_7017_: *mut LeanObject,
    mut v_x_7018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7019_: u8 = 0;
    let mut v_r_7020_: *mut LeanObject = core::ptr::null_mut();
    v_res_7019_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_7017_, v_x_7018_);
    lean_dec(v_x_7018_);
    lean_dec(v_x_7017_);
    v_r_7020_ = lean_box((v_res_7019_) as usize);
    return v_r_7020_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(
    mut v_maxPrio_x3f_7021_: *mut LeanObject,
    mut v_x_7022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: u8 = 0;
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7022_) == 0 {
                    v___x_7023_ = lean_box(0);
                    return v___x_7023_;
                } else {
                    v_head_7024_ = lean_ctor_get(v_x_7022_, 0);
                    v_tail_7025_ = lean_ctor_get(v_x_7022_, 1);
                    v_fst_7026_ = lean_ctor_get(v_head_7024_, 0);
                    lean_inc(v_fst_7026_);
                    v___x_7027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7027_, 0, v_fst_7026_);
                    v___x_7028_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_7027_, v_maxPrio_x3f_7021_);
                    lean_dec_ref_known(v___x_7027_, 1);
                    if v___x_7028_ == 0 {
                        v_x_7022_ = v_tail_7025_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_7024_);
                        v___x_7030_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7030_, 0, v_head_7024_);
                        return v___x_7030_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(
    mut v_maxPrio_x3f_7031_: *mut LeanObject,
    mut v_x_7032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7033_: *mut LeanObject = core::ptr::null_mut();
    v_res_7033_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_7031_, v_x_7032_);
    lean_dec(v_x_7032_);
    lean_dec(v_maxPrio_x3f_7031_);
    return v_res_7033_;
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(
    mut v_x_7034_: *mut LeanObject,
    mut v_x_7035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7035_) == 0 {
                    lean_inc_ref(v_x_7034_);
                    return v_x_7034_;
                } else {
                    v_head_7036_ = lean_ctor_get(v_x_7035_, 0);
                    v_tail_7037_ = lean_ctor_get(v_x_7035_, 1);
                    v___x_7038_ =
                        l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_7034_, v_head_7036_);
                    if v___x_7038_ == 2 {
                        v_x_7035_ = v_tail_7037_;
                        state = 0;
                        continue;
                    } else {
                        v_x_7034_ = v_head_7036_;
                        v_x_7035_ = v_tail_7037_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(
    mut v_x_7041_: *mut LeanObject,
    mut v_x_7042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7043_: *mut LeanObject = core::ptr::null_mut();
    v_res_7043_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_7041_, v_x_7042_);
    lean_dec(v_x_7042_);
    lean_dec_ref(v_x_7041_);
    return v_res_7043_;
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(
    mut v_x_7044_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7044_) == 0 {
        let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
        v___x_7045_ = lean_box(0);
        return v___x_7045_;
    } else {
        let mut v_head_7046_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_7047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
        v_head_7046_ = lean_ctor_get(v_x_7044_, 0);
        v_tail_7047_ = lean_ctor_get(v_x_7044_, 1);
        v___x_7048_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_7046_, v_tail_7047_);
        v___x_7049_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7049_, 0, v___x_7048_);
        return v___x_7049_;
    }
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(
    mut v_x_7050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7051_: *mut LeanObject = core::ptr::null_mut();
    v_res_7051_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_7050_);
    lean_dec(v_x_7050_);
    return v_res_7051_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(
    mut v_a_7052_: *mut LeanObject,
    mut v_a_7053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7052_) == 0 {
                    v___x_7054_ = lean_array_to_list(v_a_7053_);
                    return v___x_7054_;
                } else {
                    v_head_7055_ = lean_ctor_get(v_a_7052_, 0);
                    if lean_obj_tag(v_head_7055_) == 0 {
                        v_tail_7056_ = lean_ctor_get(v_a_7052_, 1);
                        lean_inc(v_tail_7056_);
                        lean_dec_ref_known(v_a_7052_, 2);
                        v_a_7052_ = v_tail_7056_;
                        state = 0;
                        continue;
                    } else {
                        v_val_7058_ = lean_ctor_get(v_head_7055_, 0);
                        if lean_obj_tag(v_val_7058_) == 0 {
                            v_tail_7059_ = lean_ctor_get(v_a_7052_, 1);
                            lean_inc(v_tail_7059_);
                            lean_dec_ref_known(v_a_7052_, 2);
                            v_a_7052_ = v_tail_7059_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc_ref(v_val_7058_);
                            v_tail_7061_ = lean_ctor_get(v_a_7052_, 1);
                            lean_inc(v_tail_7061_);
                            lean_dec_ref_known(v_a_7052_, 2);
                            v_val_7062_ = lean_ctor_get(v_val_7058_, 0);
                            lean_inc(v_val_7062_);
                            lean_dec_ref_known(v_val_7058_, 1);
                            v___x_7063_ = lean_array_push(v_a_7053_, v_val_7062_);
                            v_a_7052_ = v_tail_7061_;
                            v_a_7053_ = v___x_7063_;
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
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(
    mut v_a_7065_: *mut LeanObject,
    mut v_a_7066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7072_: u8 = 0;
    let mut v_fst_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7065_) == 0 {
                    v___x_7067_ = l_List_reverse___redArg(v_a_7066_);
                    return v___x_7067_;
                } else {
                    v_head_7068_ = lean_ctor_get(v_a_7065_, 0);
                    v_tail_7069_ = lean_ctor_get(v_a_7065_, 1);
                    v_isSharedCheck_7078_ = (!lean_is_exclusive(v_a_7065_)) as u8;
                    if v_isSharedCheck_7078_ == 0 {
                        v___x_7071_ = v_a_7065_;
                        v_isShared_7072_ = v_isSharedCheck_7078_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7069_);
                        lean_inc(v_head_7068_);
                        lean_dec(v_a_7065_);
                        v___x_7071_ = lean_box(0);
                        v_isShared_7072_ = v_isSharedCheck_7078_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7073_ = lean_ctor_get(v_head_7068_, 0);
                lean_inc(v_fst_7073_);
                lean_dec(v_head_7068_);
                if v_isShared_7072_ == 0 {
                    lean_ctor_set(v___x_7071_, 1, v_a_7066_);
                    lean_ctor_set(v___x_7071_, 0, v_fst_7073_);
                    v___x_7075_ = v___x_7071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_fst_7073_);
                    lean_ctor_set(v_reuseFailAlloc_7077_, 1, v_a_7066_);
                    v___x_7075_ = v_reuseFailAlloc_7077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7065_ = v_tail_7069_;
                v_a_7066_ = v___x_7075_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(
    mut v_filter_7079_: *mut LeanObject,
    mut v_hoverPos_7080_: *mut LeanObject,
    mut v_includeStop_7081_: u8,
    mut v_ctx_7082_: *mut LeanObject,
    mut v_info_7083_: *mut LeanObject,
    mut v_children_7084_: *mut LeanObject,
    mut v_results_7085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7087_: u8 = 0;
    let mut v___y_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7089_: u8 = 0;
    let mut v___y_7090_: u8 = 0;
    let mut v_priority_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7097_: u8 = 0;
    let mut v___y_7098_: u8 = 0;
    let mut v___y_7099_: u8 = 0;
    let mut v___y_7100_: u8 = 0;
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxPrio_x3f_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bestResult_x3f_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7110_: u8 = 0;
    let mut v___y_7111_: u8 = 0;
    let mut v___y_7112_: u8 = 0;
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: u8 = 0;
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: u8 = 0;
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7126_: u8 = 0;
    let mut v___x_7127_: u8 = 0;
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: u8 = 0;
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elaborator_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7101_ =
                    l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0;
                v___x_7102_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_7085_, v___x_7101_);
                lean_inc_ref(v_children_7084_);
                lean_inc_ref(v_info_7083_);
                lean_inc_ref(v_ctx_7082_);
                v___x_7103_ = lean_apply_4(
                    v_filter_7079_,
                    v_ctx_7082_,
                    v_info_7083_,
                    v_children_7084_,
                    v___x_7102_,
                );
                v___x_7104_ = lean_box(0);
                lean_inc(v___x_7103_);
                v___x_7105_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_7103_, v___x_7104_);
                v_maxPrio_x3f_7106_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_7105_);
                lean_dec(v___x_7105_);
                v_bestResult_x3f_7107_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_7106_, v___x_7103_);
                lean_dec(v___x_7103_);
                lean_dec(v_maxPrio_x3f_7106_);
                if lean_obj_tag(v_bestResult_x3f_7107_) == 1 {
                    lean_dec_ref(v_children_7084_);
                    lean_dec_ref(v_info_7083_);
                    lean_dec_ref(v_ctx_7082_);
                    return v_bestResult_x3f_7107_;
                } else {
                    lean_dec(v_bestResult_x3f_7107_);
                    v___x_7108_ = l_Lean_Elab_Info_stx(v_info_7083_);
                    v___x_7130_ =
                        l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1;
                    lean_inc(v___x_7108_);
                    v___x_7131_ = l_Lean_Syntax_isOfKind(v___x_7108_, v___x_7130_);
                    if v___x_7131_ == 0 {
                        lean_inc_ref(v_info_7083_);
                        v___x_7132_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_7083_);
                        if lean_obj_tag(v___x_7132_) == 0 {
                            v___y_7126_ = v___x_7131_;
                            state = 4;
                            continue;
                        } else {
                            v_val_7133_ = lean_ctor_get(v___x_7132_, 0);
                            lean_inc(v_val_7133_);
                            lean_dec_ref_known(v___x_7132_, 1);
                            v_elaborator_7134_ = lean_ctor_get(v_val_7133_, 0);
                            lean_inc(v_elaborator_7134_);
                            lean_dec(v_val_7133_);
                            v___x_7135_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6;
                            v___x_7136_ = lean_name_eq(v_elaborator_7134_, v___x_7135_);
                            lean_dec(v_elaborator_7134_);
                            v___y_7126_ = v___x_7136_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_7126_ = v___x_7131_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_priority_7091_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v_priority_7091_, 0, v___y_7088_);
                lean_ctor_set_uint8(
                    v_priority_7091_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_7089_,
                );
                lean_ctor_set_uint8(
                    v_priority_7091_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___y_7087_,
                );
                lean_ctor_set_uint8(
                    v_priority_7091_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___y_7090_,
                );
                v_result_7092_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v_result_7092_, 0, v_ctx_7082_);
                lean_ctor_set(v_result_7092_, 1, v_info_7083_);
                lean_ctor_set(v_result_7092_, 2, v_children_7084_);
                v___x_7093_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7093_, 0, v_priority_7091_);
                lean_ctor_set(v___x_7093_, 1, v_result_7092_);
                v___x_7094_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7094_, 0, v___x_7093_);
                return v___x_7094_;
            }
            2 => {
                if lean_obj_tag(v_info_7083_) == 2 {
                    v___y_7087_ = v___y_7100_;
                    v___y_7088_ = v___y_7096_;
                    v___y_7089_ = v___y_7097_;
                    v___y_7090_ = v___y_7099_;
                    state = 1;
                    continue;
                } else {
                    v___y_7087_ = v___y_7100_;
                    v___y_7088_ = v___y_7096_;
                    v___y_7089_ = v___y_7097_;
                    v___y_7090_ = v___y_7098_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_7113_ = l_Lean_Syntax_getRange_x3f(v___x_7108_, v___y_7111_);
                lean_dec(v___x_7108_);
                if lean_obj_tag(v___x_7113_) == 1 {
                    v_val_7114_ = lean_ctor_get(v___x_7113_, 0);
                    lean_inc(v_val_7114_);
                    lean_dec_ref_known(v___x_7113_, 1);
                    v___x_7115_ = l_Lean_Syntax_Range_contains(
                        v_val_7114_,
                        v_hoverPos_7080_,
                        v_includeStop_7081_,
                    );
                    if v___x_7115_ == 0 {
                        lean_dec(v_val_7114_);
                        lean_dec_ref(v_children_7084_);
                        lean_dec_ref(v_info_7083_);
                        lean_dec_ref(v_ctx_7082_);
                        v___x_7116_ = lean_box(0);
                        return v___x_7116_;
                    } else {
                        if v___y_7112_ == 0 {
                            lean_dec(v_val_7114_);
                            lean_dec_ref(v_children_7084_);
                            lean_dec_ref(v_info_7083_);
                            lean_dec_ref(v_ctx_7082_);
                            v___x_7117_ = lean_box(0);
                            return v___x_7117_;
                        } else {
                            v_start_7118_ = lean_ctor_get(v_val_7114_, 0);
                            lean_inc(v_start_7118_);
                            v_stop_7119_ = lean_ctor_get(v_val_7114_, 1);
                            lean_inc(v_stop_7119_);
                            lean_dec(v_val_7114_);
                            v___x_7120_ = lean_nat_dec_eq(v_stop_7119_, v_hoverPos_7080_);
                            v___x_7121_ = lean_nat_sub(v_stop_7119_, v_start_7118_);
                            lean_dec(v_start_7118_);
                            lean_dec(v_stop_7119_);
                            if lean_obj_tag(v_info_7083_) == 1 {
                                v_i_7122_ = lean_ctor_get(v_info_7083_, 0);
                                v_expr_7123_ = lean_ctor_get(v_i_7122_, 3);
                                if lean_obj_tag(v_expr_7123_) == 1 {
                                    v___y_7096_ = v___x_7121_;
                                    v___y_7097_ = v___x_7120_;
                                    v___y_7098_ = v___y_7110_;
                                    v___y_7099_ = v___y_7111_;
                                    v___y_7100_ = v___y_7111_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___y_7096_ = v___x_7121_;
                                    v___y_7097_ = v___x_7120_;
                                    v___y_7098_ = v___y_7110_;
                                    v___y_7099_ = v___y_7111_;
                                    v___y_7100_ = v___y_7110_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_7096_ = v___x_7121_;
                                v___y_7097_ = v___x_7120_;
                                v___y_7098_ = v___y_7110_;
                                v___y_7099_ = v___y_7111_;
                                v___y_7100_ = v___y_7110_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_7113_);
                    lean_dec_ref(v_children_7084_);
                    lean_dec_ref(v_info_7083_);
                    lean_dec_ref(v_ctx_7082_);
                    v___x_7124_ = lean_box(0);
                    return v___x_7124_;
                }
            }
            4 => {
                if v___y_7126_ == 0 {
                    v___x_7127_ = 1;
                    match lean_obj_tag(v_info_7083_) {
                        7 => {
                            v___y_7110_ = v___y_7126_;
                            v___y_7111_ = v___x_7127_;
                            v___y_7112_ = v___x_7127_;
                            state = 3;
                            continue;
                        }
                        5 => {
                            v___y_7110_ = v___y_7126_;
                            v___y_7111_ = v___x_7127_;
                            v___y_7112_ = v___x_7127_;
                            state = 3;
                            continue;
                        }
                        6 => {
                            v___y_7110_ = v___y_7126_;
                            v___y_7111_ = v___x_7127_;
                            v___y_7112_ = v___x_7127_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            lean_inc_ref(v_info_7083_);
                            v___x_7128_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_7083_);
                            if lean_obj_tag(v___x_7128_) == 0 {
                                v___y_7110_ = v___y_7126_;
                                v___y_7111_ = v___x_7127_;
                                v___y_7112_ = v___y_7126_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_7128_, 1);
                                v___y_7110_ = v___y_7126_;
                                v___y_7111_ = v___x_7127_;
                                v___y_7112_ = v___x_7127_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_7108_);
                    lean_dec_ref(v_children_7084_);
                    lean_dec_ref(v_info_7083_);
                    lean_dec_ref(v_ctx_7082_);
                    v___x_7129_ = lean_box(0);
                    return v___x_7129_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(
    mut v_filter_7137_: *mut LeanObject,
    mut v_hoverPos_7138_: *mut LeanObject,
    mut v_includeStop_7139_: *mut LeanObject,
    mut v_ctx_7140_: *mut LeanObject,
    mut v_info_7141_: *mut LeanObject,
    mut v_children_7142_: *mut LeanObject,
    mut v_results_7143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_7144_: u8 = 0;
    let mut v_res_7145_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_7144_ = (lean_unbox(v_includeStop_7139_) as u8);
    v_res_7145_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_7137_, v_hoverPos_7138_, v_includeStop_boxed_7144_, v_ctx_7140_, v_info_7141_, v_children_7142_, v_results_7143_);
    lean_dec(v_hoverPos_7138_);
    return v_res_7145_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(
    mut v_t_7146_: *mut LeanObject,
    mut v_hoverPos_7147_: *mut LeanObject,
    mut v_includeStop_7148_: u8,
    mut v_filter_7149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postNode_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v_snd_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: u8 = 0;
    let mut v_reuseFailAlloc_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7150_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0;
                v___x_7151_ = lean_box((v_includeStop_7148_) as usize);
                v_postNode_7152_ = lean_alloc_closure(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed as *mut core::ffi::c_void, 7, 3);
                lean_closure_set(v_postNode_7152_, 0, v_filter_7149_);
                lean_closure_set(v_postNode_7152_, 1, v_hoverPos_7147_);
                lean_closure_set(v_postNode_7152_, 2, v___x_7151_);
                v___x_7153_ = lean_box(0);
                v___x_7154_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_7150_, v_postNode_7152_, v___x_7153_, v_t_7146_);
                if lean_obj_tag(v___x_7154_) == 0 {
                    return v___x_7153_;
                } else {
                    v_val_7155_ = lean_ctor_get(v___x_7154_, 0);
                    lean_inc(v_val_7155_);
                    lean_dec_ref_known(v___x_7154_, 1);
                    if lean_obj_tag(v_val_7155_) == 0 {
                        return v___x_7153_;
                    } else {
                        v_val_7156_ = lean_ctor_get(v_val_7155_, 0);
                        v_isSharedCheck_7168_ = (!lean_is_exclusive(v_val_7155_)) as u8;
                        if v_isSharedCheck_7168_ == 0 {
                            v___x_7158_ = v_val_7155_;
                            v_isShared_7159_ = v_isSharedCheck_7168_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_7156_);
                            lean_dec(v_val_7155_);
                            v___x_7158_ = lean_box(0);
                            v_isShared_7159_ = v_isSharedCheck_7168_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_7160_ = lean_ctor_get(v_val_7156_, 1);
                lean_inc(v_snd_7160_);
                lean_dec(v_val_7156_);
                v_info_7161_ = lean_ctor_get(v_snd_7160_, 1);
                lean_inc_ref(v_info_7161_);
                if v_isShared_7159_ == 0 {
                    lean_ctor_set(v___x_7158_, 0, v_snd_7160_);
                    v___x_7163_ = v___x_7158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7167_, 0, v_snd_7160_);
                    v___x_7163_ = v_reuseFailAlloc_7167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_info_7161_) == 1 {
                    v_i_7164_ = lean_ctor_get(v_info_7161_, 0);
                    lean_inc_ref(v_i_7164_);
                    lean_dec_ref_known(v_info_7161_, 1);
                    v_expr_7165_ = lean_ctor_get(v_i_7164_, 3);
                    lean_inc_ref(v_expr_7165_);
                    lean_dec_ref(v_i_7164_);
                    v___x_7166_ = l_Lean_Expr_isSyntheticSorry(v_expr_7165_);
                    lean_dec_ref(v_expr_7165_);
                    if v___x_7166_ == 0 {
                        return v___x_7163_;
                    } else {
                        lean_dec_ref(v___x_7163_);
                        return v___x_7153_;
                    }
                } else {
                    lean_dec_ref(v_info_7161_);
                    return v___x_7163_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(
    mut v_t_7169_: *mut LeanObject,
    mut v_hoverPos_7170_: *mut LeanObject,
    mut v_includeStop_7171_: *mut LeanObject,
    mut v_filter_7172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeStop_boxed_7173_: u8 = 0;
    let mut v_res_7174_: *mut LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_7173_ = (lean_unbox(v_includeStop_7171_) as u8);
    v_res_7174_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_7169_, v_hoverPos_7170_, v_includeStop_boxed_7173_, v_filter_7172_);
    return v_res_7174_;
}
pub unsafe fn l_Lean_Elab_InfoTree_termGoalAt_x3f(
    mut v_t_7176_: *mut LeanObject,
    mut v_hoverPos_7177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: u8 = 0;
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    v_filter_7178_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0;
    v___x_7179_ = 1;
    v___x_7180_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_7176_, v_hoverPos_7177_, v___x_7179_, v_filter_7178_);
    return v___x_7180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_InfoUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_instLEHoverableInfoPrio = _init_l_Lean_Elab_instLEHoverableInfoPrio();
    lean_mark_persistent(l_Lean_Elab_instLEHoverableInfoPrio);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_InfoUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_InfoUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_InfoUtils(builtin);
}
