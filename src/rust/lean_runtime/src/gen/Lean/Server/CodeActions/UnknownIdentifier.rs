// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: Lean.Server.Completion.CompletionInfoSelection Lean.Server.CodeActions.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Lsp::Basic::l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit;
use crate::r#gen::Lean::Data::Lsp::Internal::{
    l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson,
    l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::{
    l_Lean_FileMap_utf8PosToLspPos, l_Lean_FileMap_utf8RangeToLspRange,
};
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_getPrefix, l_Lean_Name_getString_x21, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_empty;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_ofPosition;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_ContextInfo_runMetaM___redArg;
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_mainModule};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar};
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_SnapshotTask_map___redArg, l_Lean_Language_SnapshotTree_getAll,
};
use crate::r#gen::Lean::Language::Lean::Types::{
    l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go,
    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go,
    l_Lean_Language_Lean_pushOpt___redArg,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_hasTag, l_Lean_MessageLog_append};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Server::AsyncList::l_IO_AsyncList_waitAll___redArg;
use crate::r#gen::Lean::Server::CodeActions::Basic::{
    initialize_Lean_Server_CodeActions_Basic, l_Lean_Server_instToJsonCodeActionResolveData_toJson,
    runtime_initialize_Lean_Server_CodeActions_Basic,
};
use crate::r#gen::Lean::Server::Completion::CompletionInfoSelection::{
    initialize_Lean_Server_Completion_CompletionInfoSelection,
    l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt,
    runtime_initialize_Lean_Server_Completion_CompletionInfoSelection,
};
use crate::r#gen::Lean::Server::Completion::CompletionUtils::{
    l_Lean_Server_Completion_getDotCompletionTypeNames,
    l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed,
    l_Lean_Server_Completion_minimizeGlobalIdentifierInContext,
};
use crate::r#gen::Lean::Server::FileWorker::Utils::l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier;
use crate::r#gen::Lean::Server::InfoUtils::l_Lean_Elab_InfoTree_foldInfo___redArg;
use crate::r#gen::Lean::Server::RequestCancellation::l_Lean_Server_RequestCancellationToken_requestCancellationTask;
use crate::r#gen::Lean::Server::Requests::{
    l_Lean_Language_SnapshotTree_collectMessagesInRange,
    l_Lean_Language_SnapshotTree_foldInfosInRange___redArg, l_Lean_Server_RequestError_ofIoError,
    l_Lean_Server_RequestM_checkCancelled, l_Lean_Server_RequestM_findCmdDataAtPos,
    l_Lean_Server_RequestM_findCmdParsedSnap,
};
use crate::r#gen::Lean::Server::ServerTask::{
    l_Lean_Server_ServerTask_mapCheap___redArg, l_Lean_Server_ServerTask_waitAny___redArg,
};
use crate::r#gen::Lean::Server::Snapshots::l_Lean_Server_Snapshots_Snapshot_infoTree;
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_Range_overlaps, l_Lean_Syntax_getRange_x3f};
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value:
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
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value:
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
    m_fun: l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value:
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
    m_fun: l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value:
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
static mut l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_computeQueries___closed__0_value:
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
static mut l_Lean_Server_FileWorker_computeQueries___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_computeQueries___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        97, 108, 108, 85, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101,
        114, 115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value:
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
            l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        2250887845330408536 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value:
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
        117, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value:
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
            l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        16966433945472317273 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        73, 109, 112, 111, 114, 116, 32, 97, 108, 108, 32, 117, 110, 97, 109, 98, 105, 103, 117,
        111, 117, 115, 32, 117, 110, 107, 110, 111, 119, 110, 32, 105, 100, 101, 110, 116, 105,
        102, 105, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 98, 108, 105, 99, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 101, 116, 97, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 115, 101, 114, 118, 101, 114, 32, 114, 101, 113, 117, 101, 115, 116, 32, 114, 101, 115, 112, 111, 110, 115, 101, 58, 32, 0]};
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 104, 97, 110, 103, 101, 32, 116, 111, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 102, 114, 111, 109, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value:
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
        36, 47, 108, 101, 97, 110, 47, 113, 117, 101, 114, 121, 77, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value:
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
    m_fun: l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value:
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
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value:
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
    m_data: [113, 117, 105, 99, 107, 102, 105, 120, 0],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(
    mut v_r1_2868_: *mut crate::leanh::LeanObject,
    mut v_r2_2869_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_start_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    v_start_2870_ = crate::leanh::lean_ctor_get(v_r1_2868_, 0);
    v_stop_2871_ = crate::leanh::lean_ctor_get(v_r1_2868_, 1);
    v_start_2872_ = crate::leanh::lean_ctor_get(v_r2_2869_, 0);
    v_stop_2873_ = crate::leanh::lean_ctor_get(v_r2_2869_, 1);
    v___x_2874_ = lean_nat_dec_lt(v_start_2870_, v_start_2872_);
    if v___x_2874_ == 0 {
        let mut v___x_2875_: u8 = 0;
        v___x_2875_ = lean_nat_dec_lt(v_start_2872_, v_start_2870_);
        if v___x_2875_ == 0 {
            let mut v___x_2876_: u8 = 0;
            v___x_2876_ = lean_nat_dec_lt(v_stop_2871_, v_stop_2873_);
            if v___x_2876_ == 0 {
                let mut v___x_2877_: u8 = 0;
                v___x_2877_ = lean_nat_dec_lt(v_stop_2873_, v_stop_2871_);
                if v___x_2877_ == 0 {
                    let mut v___x_2878_: u8 = 0;
                    v___x_2878_ = 1;
                    return v___x_2878_;
                } else {
                    let mut v___x_2879_: u8 = 0;
                    v___x_2879_ = 2;
                    return v___x_2879_;
                }
            } else {
                let mut v___x_2880_: u8 = 0;
                v___x_2880_ = 0;
                return v___x_2880_;
            }
        } else {
            let mut v___x_2881_: u8 = 0;
            v___x_2881_ = 2;
            return v___x_2881_;
        }
    } else {
        let mut v___x_2882_: u8 = 0;
        v___x_2882_ = 0;
        return v___x_2882_;
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges___boxed(
    mut v_r1_2883_: *mut crate::leanh::LeanObject,
    mut v_r2_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2885_: u8 = 0;
    let mut v_r_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2885_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_r1_2883_, v_r2_2884_);
    crate::leanh::lean_dec_ref(v_r2_2884_);
    crate::leanh::lean_dec_ref(v_r1_2883_);
    v_r_2886_ = crate::leanh::lean_box((v_res_2885_) as usize);
    return v_r_2886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(
    mut v_k_2887_: *mut crate::leanh::LeanObject,
    mut v_t_2888_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2888_) == 0 {
                    v_k_2889_ = crate::leanh::lean_ctor_get(v_t_2888_, 1);
                    v_l_2890_ = crate::leanh::lean_ctor_get(v_t_2888_, 3);
                    v_r_2891_ = crate::leanh::lean_ctor_get(v_t_2888_, 4);
                    v___x_2892_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_2887_, v_k_2889_);
                    match v___x_2892_ {
                        0 => {
                            v_t_2888_ = v_l_2890_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2894_ = 1;
                            return v___x_2894_;
                        }
                        _ => {
                            v_t_2888_ = v_r_2891_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2896_ = 0;
                    return v___x_2896_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg___boxed(
    mut v_k_2897_: *mut crate::leanh::LeanObject,
    mut v_t_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_2897_, v_t_2898_);
    crate::leanh::lean_dec(v_t_2898_);
    crate::leanh::lean_dec_ref(v_k_2897_);
    v_r_2900_ = crate::leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(
    mut v_k_2901_: *mut crate::leanh::LeanObject,
    mut v_v_2902_: *mut crate::leanh::LeanObject,
    mut v_t_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v_impl_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_size_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_unused_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v_k_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v_unused_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_unused_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v_size_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_unused_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_unused_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v_k_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_unused_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_unused_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v_unused_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2903_) == 0 {
                    v_size_2904_ = crate::leanh::lean_ctor_get(v_t_2903_, 0);
                    v_k_2905_ = crate::leanh::lean_ctor_get(v_t_2903_, 1);
                    v_v_2906_ = crate::leanh::lean_ctor_get(v_t_2903_, 2);
                    v_l_2907_ = crate::leanh::lean_ctor_get(v_t_2903_, 3);
                    v_r_2908_ = crate::leanh::lean_ctor_get(v_t_2903_, 4);
                    v_isSharedCheck_3188_ = (!crate::leanh::lean_is_exclusive(v_t_2903_)) as u8;
                    if v_isSharedCheck_3188_ == 0 {
                        v___x_2910_ = v_t_2903_;
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2908_);
                        crate::leanh::lean_inc(v_l_2907_);
                        crate::leanh::lean_inc(v_v_2906_);
                        crate::leanh::lean_inc(v_k_2905_);
                        crate::leanh::lean_inc(v_size_2904_);
                        crate::leanh::lean_dec(v_t_2903_);
                        v___x_2910_ = crate::leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3189_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3190_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3189_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 1, v_k_2901_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 2, v_v_2902_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 3, v_t_2903_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 4, v_t_2903_);
                    return v___x_3190_;
                }
            }
            1 => {
                v___x_2912_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_2901_, v_k_2905_);
                match v___x_2912_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2904_);
                        v_impl_2913_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_l_2907_);
                        v___x_2914_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_2908_) == 0 {
                            v_size_2915_ = crate::leanh::lean_ctor_get(v_r_2908_, 0);
                            v_size_2916_ = crate::leanh::lean_ctor_get(v_impl_2913_, 0);
                            crate::leanh::lean_inc(v_size_2916_);
                            v_k_2917_ = crate::leanh::lean_ctor_get(v_impl_2913_, 1);
                            crate::leanh::lean_inc(v_k_2917_);
                            v_v_2918_ = crate::leanh::lean_ctor_get(v_impl_2913_, 2);
                            crate::leanh::lean_inc(v_v_2918_);
                            v_l_2919_ = crate::leanh::lean_ctor_get(v_impl_2913_, 3);
                            crate::leanh::lean_inc(v_l_2919_);
                            v_r_2920_ = crate::leanh::lean_ctor_get(v_impl_2913_, 4);
                            crate::leanh::lean_inc(v_r_2920_);
                            v___x_2921_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2922_ = lean_nat_mul(v___x_2921_, v_size_2915_);
                            v___x_2923_ = lean_nat_dec_lt(v___x_2922_, v_size_2916_);
                            crate::leanh::lean_dec(v___x_2922_);
                            if v___x_2923_ == 0 {
                                crate::leanh::lean_dec(v_r_2920_);
                                crate::leanh::lean_dec(v_l_2919_);
                                crate::leanh::lean_dec(v_v_2918_);
                                crate::leanh::lean_dec(v_k_2917_);
                                v___x_2924_ = lean_nat_add(v___x_2914_, v_size_2916_);
                                crate::leanh::lean_dec(v_size_2916_);
                                v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2915_);
                                crate::leanh::lean_dec(v___x_2924_);
                                if v_isShared_2911_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_2925_);
                                    v___x_2927_ = v___x_2910_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2928_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        0,
                                        v___x_2925_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        1,
                                        v_k_2905_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        2,
                                        v_v_2906_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        3,
                                        v_impl_2913_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        4,
                                        v_r_2908_,
                                    );
                                    v___x_2927_ = v_reuseFailAlloc_2928_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2994_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_2994_ == 0 {
                                    v_unused_2995_ = crate::leanh::lean_ctor_get(v_impl_2913_, 4);
                                    crate::leanh::lean_dec(v_unused_2995_);
                                    v_unused_2996_ = crate::leanh::lean_ctor_get(v_impl_2913_, 3);
                                    crate::leanh::lean_dec(v_unused_2996_);
                                    v_unused_2997_ = crate::leanh::lean_ctor_get(v_impl_2913_, 2);
                                    crate::leanh::lean_dec(v_unused_2997_);
                                    v_unused_2998_ = crate::leanh::lean_ctor_get(v_impl_2913_, 1);
                                    crate::leanh::lean_dec(v_unused_2998_);
                                    v_unused_2999_ = crate::leanh::lean_ctor_get(v_impl_2913_, 0);
                                    crate::leanh::lean_dec(v_unused_2999_);
                                    v___x_2930_ = v_impl_2913_;
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2913_);
                                    v___x_2930_ = crate::leanh::lean_box(0);
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3000_ = crate::leanh::lean_ctor_get(v_impl_2913_, 3);
                            crate::leanh::lean_inc(v_l_3000_);
                            if crate::leanh::lean_obj_tag(v_l_3000_) == 0 {
                                v_r_3001_ = crate::leanh::lean_ctor_get(v_impl_2913_, 4);
                                v_k_3002_ = crate::leanh::lean_ctor_get(v_impl_2913_, 1);
                                v_v_3003_ = crate::leanh::lean_ctor_get(v_impl_2913_, 2);
                                v_isSharedCheck_3014_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_3014_ == 0 {
                                    v_unused_3015_ = crate::leanh::lean_ctor_get(v_impl_2913_, 3);
                                    crate::leanh::lean_dec(v_unused_3015_);
                                    v_unused_3016_ = crate::leanh::lean_ctor_get(v_impl_2913_, 0);
                                    crate::leanh::lean_dec(v_unused_3016_);
                                    v___x_3005_ = v_impl_2913_;
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3001_);
                                    crate::leanh::lean_inc(v_v_3003_);
                                    crate::leanh::lean_inc(v_k_3002_);
                                    crate::leanh::lean_dec(v_impl_2913_);
                                    v___x_3005_ = crate::leanh::lean_box(0);
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3017_ = crate::leanh::lean_ctor_get(v_impl_2913_, 4);
                                crate::leanh::lean_inc(v_r_3017_);
                                if crate::leanh::lean_obj_tag(v_r_3017_) == 0 {
                                    v_k_3018_ = crate::leanh::lean_ctor_get(v_impl_2913_, 1);
                                    v_v_3019_ = crate::leanh::lean_ctor_get(v_impl_2913_, 2);
                                    v_isSharedCheck_3042_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v_unused_3043_ =
                                            crate::leanh::lean_ctor_get(v_impl_2913_, 4);
                                        crate::leanh::lean_dec(v_unused_3043_);
                                        v_unused_3044_ =
                                            crate::leanh::lean_ctor_get(v_impl_2913_, 3);
                                        crate::leanh::lean_dec(v_unused_3044_);
                                        v_unused_3045_ =
                                            crate::leanh::lean_ctor_get(v_impl_2913_, 0);
                                        crate::leanh::lean_dec(v_unused_3045_);
                                        v___x_3021_ = v_impl_2913_;
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3019_);
                                        crate::leanh::lean_inc(v_k_3018_);
                                        crate::leanh::lean_dec(v_impl_2913_);
                                        v___x_3021_ = crate::leanh::lean_box(0);
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3046_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2910_, 4, v_r_3017_);
                                        crate::leanh::lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                        crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3046_);
                                        v___x_3048_ = v___x_2910_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3049_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            0,
                                            v___x_3046_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            1,
                                            v_k_2905_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            2,
                                            v_v_2906_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            3,
                                            v_impl_2913_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            4,
                                            v_r_3017_,
                                        );
                                        v___x_3048_ = v_reuseFailAlloc_3049_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2906_);
                        crate::leanh::lean_dec(v_k_2905_);
                        if v_isShared_2911_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_2902_);
                            crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_2901_);
                            v___x_3051_ = v___x_2910_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3052_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_size_2904_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_k_2901_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_v_2902_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 3, v_l_2907_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 4, v_r_2908_);
                            v___x_3051_ = v_reuseFailAlloc_3052_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2904_);
                        v_impl_3053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_r_2908_);
                        v___x_3054_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_2907_) == 0 {
                            v_size_3055_ = crate::leanh::lean_ctor_get(v_l_2907_, 0);
                            v_size_3056_ = crate::leanh::lean_ctor_get(v_impl_3053_, 0);
                            crate::leanh::lean_inc(v_size_3056_);
                            v_k_3057_ = crate::leanh::lean_ctor_get(v_impl_3053_, 1);
                            crate::leanh::lean_inc(v_k_3057_);
                            v_v_3058_ = crate::leanh::lean_ctor_get(v_impl_3053_, 2);
                            crate::leanh::lean_inc(v_v_3058_);
                            v_l_3059_ = crate::leanh::lean_ctor_get(v_impl_3053_, 3);
                            crate::leanh::lean_inc(v_l_3059_);
                            v_r_3060_ = crate::leanh::lean_ctor_get(v_impl_3053_, 4);
                            crate::leanh::lean_inc(v_r_3060_);
                            v___x_3061_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3062_ = lean_nat_mul(v___x_3061_, v_size_3055_);
                            v___x_3063_ = lean_nat_dec_lt(v___x_3062_, v_size_3056_);
                            crate::leanh::lean_dec(v___x_3062_);
                            if v___x_3063_ == 0 {
                                crate::leanh::lean_dec(v_r_3060_);
                                crate::leanh::lean_dec(v_l_3059_);
                                crate::leanh::lean_dec(v_v_3058_);
                                crate::leanh::lean_dec(v_k_3057_);
                                v___x_3064_ = lean_nat_add(v___x_3054_, v_size_3055_);
                                v___x_3065_ = lean_nat_add(v___x_3064_, v_size_3056_);
                                crate::leanh::lean_dec(v_size_3056_);
                                crate::leanh::lean_dec(v___x_3064_);
                                if v_isShared_2911_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3065_);
                                    v___x_3067_ = v___x_2910_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3068_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        0,
                                        v___x_3065_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        1,
                                        v_k_2905_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        2,
                                        v_v_2906_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        3,
                                        v_l_2907_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        4,
                                        v_impl_3053_,
                                    );
                                    v___x_3067_ = v_reuseFailAlloc_3068_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3132_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3132_ == 0 {
                                    v_unused_3133_ = crate::leanh::lean_ctor_get(v_impl_3053_, 4);
                                    crate::leanh::lean_dec(v_unused_3133_);
                                    v_unused_3134_ = crate::leanh::lean_ctor_get(v_impl_3053_, 3);
                                    crate::leanh::lean_dec(v_unused_3134_);
                                    v_unused_3135_ = crate::leanh::lean_ctor_get(v_impl_3053_, 2);
                                    crate::leanh::lean_dec(v_unused_3135_);
                                    v_unused_3136_ = crate::leanh::lean_ctor_get(v_impl_3053_, 1);
                                    crate::leanh::lean_dec(v_unused_3136_);
                                    v_unused_3137_ = crate::leanh::lean_ctor_get(v_impl_3053_, 0);
                                    crate::leanh::lean_dec(v_unused_3137_);
                                    v___x_3070_ = v_impl_3053_;
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_3053_);
                                    v___x_3070_ = crate::leanh::lean_box(0);
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3138_ = crate::leanh::lean_ctor_get(v_impl_3053_, 3);
                            crate::leanh::lean_inc(v_l_3138_);
                            if crate::leanh::lean_obj_tag(v_l_3138_) == 0 {
                                v_r_3139_ = crate::leanh::lean_ctor_get(v_impl_3053_, 4);
                                v_k_3140_ = crate::leanh::lean_ctor_get(v_impl_3053_, 1);
                                v_v_3141_ = crate::leanh::lean_ctor_get(v_impl_3053_, 2);
                                v_isSharedCheck_3164_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3164_ == 0 {
                                    v_unused_3165_ = crate::leanh::lean_ctor_get(v_impl_3053_, 3);
                                    crate::leanh::lean_dec(v_unused_3165_);
                                    v_unused_3166_ = crate::leanh::lean_ctor_get(v_impl_3053_, 0);
                                    crate::leanh::lean_dec(v_unused_3166_);
                                    v___x_3143_ = v_impl_3053_;
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3139_);
                                    crate::leanh::lean_inc(v_v_3141_);
                                    crate::leanh::lean_inc(v_k_3140_);
                                    crate::leanh::lean_dec(v_impl_3053_);
                                    v___x_3143_ = crate::leanh::lean_box(0);
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3167_ = crate::leanh::lean_ctor_get(v_impl_3053_, 4);
                                crate::leanh::lean_inc(v_r_3167_);
                                if crate::leanh::lean_obj_tag(v_r_3167_) == 0 {
                                    v_k_3168_ = crate::leanh::lean_ctor_get(v_impl_3053_, 1);
                                    v_v_3169_ = crate::leanh::lean_ctor_get(v_impl_3053_, 2);
                                    v_isSharedCheck_3180_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                    if v_isSharedCheck_3180_ == 0 {
                                        v_unused_3181_ =
                                            crate::leanh::lean_ctor_get(v_impl_3053_, 4);
                                        crate::leanh::lean_dec(v_unused_3181_);
                                        v_unused_3182_ =
                                            crate::leanh::lean_ctor_get(v_impl_3053_, 3);
                                        crate::leanh::lean_dec(v_unused_3182_);
                                        v_unused_3183_ =
                                            crate::leanh::lean_ctor_get(v_impl_3053_, 0);
                                        crate::leanh::lean_dec(v_unused_3183_);
                                        v___x_3171_ = v_impl_3053_;
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3169_);
                                        crate::leanh::lean_inc(v_k_3168_);
                                        crate::leanh::lean_dec(v_impl_3053_);
                                        v___x_3171_ = crate::leanh::lean_box(0);
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3184_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                        crate::leanh::lean_ctor_set(v___x_2910_, 3, v_r_3167_);
                                        crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3184_);
                                        v___x_3186_ = v___x_2910_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3187_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            0,
                                            v___x_3184_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            1,
                                            v_k_2905_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            2,
                                            v_v_2906_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            3,
                                            v_r_3167_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            4,
                                            v_impl_3053_,
                                        );
                                        v___x_3186_ = v_reuseFailAlloc_3187_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2927_;
            }
            3 => {
                v_size_2932_ = crate::leanh::lean_ctor_get(v_l_2919_, 0);
                v_size_2933_ = crate::leanh::lean_ctor_get(v_r_2920_, 0);
                v_k_2934_ = crate::leanh::lean_ctor_get(v_r_2920_, 1);
                v_v_2935_ = crate::leanh::lean_ctor_get(v_r_2920_, 2);
                v_l_2936_ = crate::leanh::lean_ctor_get(v_r_2920_, 3);
                v_r_2937_ = crate::leanh::lean_ctor_get(v_r_2920_, 4);
                v___x_2938_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
                v___x_2940_ = lean_nat_dec_lt(v_size_2933_, v___x_2939_);
                crate::leanh::lean_dec(v___x_2939_);
                if v___x_2940_ == 0 {
                    crate::leanh::lean_inc(v_r_2937_);
                    crate::leanh::lean_inc(v_l_2936_);
                    crate::leanh::lean_inc(v_v_2935_);
                    crate::leanh::lean_inc(v_k_2934_);
                    v_isSharedCheck_2969_ = (!crate::leanh::lean_is_exclusive(v_r_2920_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v_unused_2970_ = crate::leanh::lean_ctor_get(v_r_2920_, 4);
                        crate::leanh::lean_dec(v_unused_2970_);
                        v_unused_2971_ = crate::leanh::lean_ctor_get(v_r_2920_, 3);
                        crate::leanh::lean_dec(v_unused_2971_);
                        v_unused_2972_ = crate::leanh::lean_ctor_get(v_r_2920_, 2);
                        crate::leanh::lean_dec(v_unused_2972_);
                        v_unused_2973_ = crate::leanh::lean_ctor_get(v_r_2920_, 1);
                        crate::leanh::lean_dec(v_unused_2973_);
                        v_unused_2974_ = crate::leanh::lean_ctor_get(v_r_2920_, 0);
                        crate::leanh::lean_dec(v_unused_2974_);
                        v___x_2942_ = v_r_2920_;
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2920_);
                        v___x_2942_ = crate::leanh::lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2910_);
                    v___x_2975_ = lean_nat_add(v___x_2914_, v_size_2916_);
                    crate::leanh::lean_dec(v_size_2916_);
                    v___x_2976_ = lean_nat_add(v___x_2975_, v_size_2915_);
                    crate::leanh::lean_dec(v___x_2975_);
                    v___x_2977_ = lean_nat_add(v___x_2914_, v_size_2915_);
                    v___x_2978_ = lean_nat_add(v___x_2977_, v_size_2933_);
                    crate::leanh::lean_dec(v___x_2977_);
                    crate::leanh::lean_inc_ref(v_r_2908_);
                    if v_isShared_2931_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2930_, 4, v_r_2908_);
                        crate::leanh::lean_ctor_set(v___x_2930_, 3, v_r_2920_);
                        crate::leanh::lean_ctor_set(v___x_2930_, 2, v_v_2906_);
                        crate::leanh::lean_ctor_set(v___x_2930_, 1, v_k_2905_);
                        crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2978_);
                        v___x_2980_ = v___x_2930_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2978_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2906_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_r_2920_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_r_2908_);
                        v___x_2980_ = v_reuseFailAlloc_2993_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2944_ = lean_nat_add(v___x_2914_, v_size_2916_);
                crate::leanh::lean_dec(v_size_2916_);
                v___x_2945_ = lean_nat_add(v___x_2944_, v_size_2915_);
                crate::leanh::lean_dec(v___x_2944_);
                v___x_2957_ = lean_nat_add(v___x_2914_, v_size_2932_);
                if crate::leanh::lean_obj_tag(v_l_2936_) == 0 {
                    v_size_2967_ = crate::leanh::lean_ctor_get(v_l_2936_, 0);
                    crate::leanh::lean_inc(v_size_2967_);
                    v___y_2959_ = v_size_2967_;
                    state = 8;
                    continue;
                } else {
                    v___x_2968_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2959_ = v___x_2968_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2950_ = lean_nat_add(v___y_2948_, v___y_2949_);
                crate::leanh::lean_dec(v___y_2949_);
                crate::leanh::lean_dec(v___y_2948_);
                if v_isShared_2943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2942_, 4, v_r_2908_);
                    crate::leanh::lean_ctor_set(v___x_2942_, 3, v_r_2937_);
                    crate::leanh::lean_ctor_set(v___x_2942_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v___x_2942_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v___x_2942_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_r_2937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_r_2908_);
                    v___x_2952_ = v_reuseFailAlloc_2956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2930_, 4, v___x_2952_);
                    crate::leanh::lean_ctor_set(v___x_2930_, 3, v___y_2947_);
                    crate::leanh::lean_ctor_set(v___x_2930_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v___x_2930_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2945_);
                    v___x_2954_ = v___x_2930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 3, v___y_2947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 4, v___x_2952_);
                    v___x_2954_ = v_reuseFailAlloc_2955_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2954_;
            }
            8 => {
                v___x_2960_ = lean_nat_add(v___x_2957_, v___y_2959_);
                crate::leanh::lean_dec(v___y_2959_);
                crate::leanh::lean_dec(v___x_2957_);
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v_l_2936_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v_l_2919_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2910_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_l_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_l_2936_);
                    v___x_2962_ = v_reuseFailAlloc_2966_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2963_ = lean_nat_add(v___x_2914_, v_size_2915_);
                if crate::leanh::lean_obj_tag(v_r_2937_) == 0 {
                    v_size_2964_ = crate::leanh::lean_ctor_get(v_r_2937_, 0);
                    crate::leanh::lean_inc(v_size_2964_);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v_size_2964_;
                    state = 5;
                    continue;
                } else {
                    v___x_2965_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v___x_2965_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2987_ = (!crate::leanh::lean_is_exclusive(v_r_2908_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v_unused_2988_ = crate::leanh::lean_ctor_get(v_r_2908_, 4);
                    crate::leanh::lean_dec(v_unused_2988_);
                    v_unused_2989_ = crate::leanh::lean_ctor_get(v_r_2908_, 3);
                    crate::leanh::lean_dec(v_unused_2989_);
                    v_unused_2990_ = crate::leanh::lean_ctor_get(v_r_2908_, 2);
                    crate::leanh::lean_dec(v_unused_2990_);
                    v_unused_2991_ = crate::leanh::lean_ctor_get(v_r_2908_, 1);
                    crate::leanh::lean_dec(v_unused_2991_);
                    v_unused_2992_ = crate::leanh::lean_ctor_get(v_r_2908_, 0);
                    crate::leanh::lean_dec(v_unused_2992_);
                    v___x_2982_ = v_r_2908_;
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2908_);
                    v___x_2982_ = crate::leanh::lean_box(0);
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2983_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2982_, 4, v___x_2980_);
                    crate::leanh::lean_ctor_set(v___x_2982_, 3, v_l_2919_);
                    crate::leanh::lean_ctor_set(v___x_2982_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v___x_2982_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_2976_);
                    v___x_2985_ = v___x_2982_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_l_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2985_;
            }
            13 => {
                v___x_3007_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_3001_);
                if v_isShared_3006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3005_, 3, v_r_3001_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 0, v___x_2914_);
                    v___x_3009_ = v___x_3005_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_r_3001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_r_3001_);
                    v___x_3009_ = v_reuseFailAlloc_3013_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v___x_3009_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v_l_3000_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_3003_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_3002_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3007_);
                    v___x_3011_ = v___x_2910_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_3002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_3003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_3000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___x_3009_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3011_;
            }
            16 => {
                v_k_3023_ = crate::leanh::lean_ctor_get(v_r_3017_, 1);
                v_v_3024_ = crate::leanh::lean_ctor_get(v_r_3017_, 2);
                v_isSharedCheck_3038_ = (!crate::leanh::lean_is_exclusive(v_r_3017_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v_unused_3039_ = crate::leanh::lean_ctor_get(v_r_3017_, 4);
                    crate::leanh::lean_dec(v_unused_3039_);
                    v_unused_3040_ = crate::leanh::lean_ctor_get(v_r_3017_, 3);
                    crate::leanh::lean_dec(v_unused_3040_);
                    v_unused_3041_ = crate::leanh::lean_ctor_get(v_r_3017_, 0);
                    crate::leanh::lean_dec(v_unused_3041_);
                    v___x_3026_ = v_r_3017_;
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3024_);
                    crate::leanh::lean_inc(v_k_3023_);
                    crate::leanh::lean_dec(v_r_3017_);
                    v___x_3026_ = crate::leanh::lean_box(0);
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3028_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3026_, 4, v_l_3000_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 3, v_l_3000_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 2, v_v_3019_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 1, v_k_3018_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 0, v___x_2914_);
                    v___x_3030_ = v___x_3026_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_k_3018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_v_3019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_l_3000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_l_3000_);
                    v___x_3030_ = v_reuseFailAlloc_3037_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3021_, 4, v_l_3000_);
                    crate::leanh::lean_ctor_set(v___x_3021_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v___x_3021_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v___x_3021_, 0, v___x_2914_);
                    v___x_3032_ = v___x_3021_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_3000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_l_3000_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v___x_3032_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v___x_3030_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_3024_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_3023_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3028_);
                    v___x_3034_ = v___x_2910_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 3, v___x_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 4, v___x_3032_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3034_;
            }
            21 => {
                return v___x_3048_;
            }
            22 => {
                return v___x_3051_;
            }
            23 => {
                return v___x_3067_;
            }
            24 => {
                v_size_3072_ = crate::leanh::lean_ctor_get(v_l_3059_, 0);
                v_k_3073_ = crate::leanh::lean_ctor_get(v_l_3059_, 1);
                v_v_3074_ = crate::leanh::lean_ctor_get(v_l_3059_, 2);
                v_l_3075_ = crate::leanh::lean_ctor_get(v_l_3059_, 3);
                v_r_3076_ = crate::leanh::lean_ctor_get(v_l_3059_, 4);
                v_size_3077_ = crate::leanh::lean_ctor_get(v_r_3060_, 0);
                v___x_3078_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3079_ = lean_nat_mul(v___x_3078_, v_size_3077_);
                v___x_3080_ = lean_nat_dec_lt(v_size_3072_, v___x_3079_);
                crate::leanh::lean_dec(v___x_3079_);
                if v___x_3080_ == 0 {
                    crate::leanh::lean_inc(v_r_3076_);
                    crate::leanh::lean_inc(v_l_3075_);
                    crate::leanh::lean_inc(v_v_3074_);
                    crate::leanh::lean_inc(v_k_3073_);
                    v_isSharedCheck_3108_ = (!crate::leanh::lean_is_exclusive(v_l_3059_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v_unused_3109_ = crate::leanh::lean_ctor_get(v_l_3059_, 4);
                        crate::leanh::lean_dec(v_unused_3109_);
                        v_unused_3110_ = crate::leanh::lean_ctor_get(v_l_3059_, 3);
                        crate::leanh::lean_dec(v_unused_3110_);
                        v_unused_3111_ = crate::leanh::lean_ctor_get(v_l_3059_, 2);
                        crate::leanh::lean_dec(v_unused_3111_);
                        v_unused_3112_ = crate::leanh::lean_ctor_get(v_l_3059_, 1);
                        crate::leanh::lean_dec(v_unused_3112_);
                        v_unused_3113_ = crate::leanh::lean_ctor_get(v_l_3059_, 0);
                        crate::leanh::lean_dec(v_unused_3113_);
                        v___x_3082_ = v_l_3059_;
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3059_);
                        v___x_3082_ = crate::leanh::lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2910_);
                    v___x_3114_ = lean_nat_add(v___x_3054_, v_size_3055_);
                    v___x_3115_ = lean_nat_add(v___x_3114_, v_size_3056_);
                    crate::leanh::lean_dec(v_size_3056_);
                    v___x_3116_ = lean_nat_add(v___x_3114_, v_size_3072_);
                    crate::leanh::lean_dec(v___x_3114_);
                    crate::leanh::lean_inc_ref(v_l_2907_);
                    if v_isShared_3071_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3070_, 4, v_l_3059_);
                        crate::leanh::lean_ctor_set(v___x_3070_, 3, v_l_2907_);
                        crate::leanh::lean_ctor_set(v___x_3070_, 2, v_v_2906_);
                        crate::leanh::lean_ctor_set(v___x_3070_, 1, v_k_2905_);
                        crate::leanh::lean_ctor_set(v___x_3070_, 0, v___x_3116_);
                        v___x_3118_ = v___x_3070_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3131_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_2905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_2906_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_l_2907_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3059_);
                        v___x_3118_ = v_reuseFailAlloc_3131_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3084_ = lean_nat_add(v___x_3054_, v_size_3055_);
                v___x_3085_ = lean_nat_add(v___x_3084_, v_size_3056_);
                crate::leanh::lean_dec(v_size_3056_);
                if crate::leanh::lean_obj_tag(v_l_3075_) == 0 {
                    v_size_3106_ = crate::leanh::lean_ctor_get(v_l_3075_, 0);
                    crate::leanh::lean_inc(v_size_3106_);
                    v___y_3098_ = v_size_3106_;
                    state = 29;
                    continue;
                } else {
                    v___x_3107_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3098_ = v___x_3107_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3090_ = lean_nat_add(v___y_3087_, v___y_3089_);
                crate::leanh::lean_dec(v___y_3089_);
                crate::leanh::lean_dec(v___y_3087_);
                if v_isShared_3083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3082_, 4, v_r_3060_);
                    crate::leanh::lean_ctor_set(v___x_3082_, 3, v_r_3076_);
                    crate::leanh::lean_ctor_set(v___x_3082_, 2, v_v_3058_);
                    crate::leanh::lean_ctor_set(v___x_3082_, 1, v_k_3057_);
                    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3090_);
                    v___x_3092_ = v___x_3082_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_r_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_r_3060_);
                    v___x_3092_ = v_reuseFailAlloc_3096_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3070_, 4, v___x_3092_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 3, v___y_3088_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 2, v_v_3074_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 1, v_k_3073_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 0, v___x_3085_);
                    v___x_3094_ = v___x_3070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_k_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_v_3074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 3, v___y_3088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 4, v___x_3092_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3094_;
            }
            29 => {
                v___x_3099_ = lean_nat_add(v___x_3084_, v___y_3098_);
                crate::leanh::lean_dec(v___y_3098_);
                crate::leanh::lean_dec(v___x_3084_);
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v_l_3075_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3099_);
                    v___x_3101_ = v___x_2910_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_l_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_l_3075_);
                    v___x_3101_ = v_reuseFailAlloc_3105_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3102_ = lean_nat_add(v___x_3054_, v_size_3077_);
                if crate::leanh::lean_obj_tag(v_r_3076_) == 0 {
                    v_size_3103_ = crate::leanh::lean_ctor_get(v_r_3076_, 0);
                    crate::leanh::lean_inc(v_size_3103_);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v_size_3103_;
                    state = 26;
                    continue;
                } else {
                    v___x_3104_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v___x_3104_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3125_ = (!crate::leanh::lean_is_exclusive(v_l_2907_)) as u8;
                if v_isSharedCheck_3125_ == 0 {
                    v_unused_3126_ = crate::leanh::lean_ctor_get(v_l_2907_, 4);
                    crate::leanh::lean_dec(v_unused_3126_);
                    v_unused_3127_ = crate::leanh::lean_ctor_get(v_l_2907_, 3);
                    crate::leanh::lean_dec(v_unused_3127_);
                    v_unused_3128_ = crate::leanh::lean_ctor_get(v_l_2907_, 2);
                    crate::leanh::lean_dec(v_unused_3128_);
                    v_unused_3129_ = crate::leanh::lean_ctor_get(v_l_2907_, 1);
                    crate::leanh::lean_dec(v_unused_3129_);
                    v_unused_3130_ = crate::leanh::lean_ctor_get(v_l_2907_, 0);
                    crate::leanh::lean_dec(v_unused_3130_);
                    v___x_3120_ = v_l_2907_;
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2907_);
                    v___x_3120_ = crate::leanh::lean_box(0);
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3120_, 4, v_r_3060_);
                    crate::leanh::lean_ctor_set(v___x_3120_, 3, v___x_3118_);
                    crate::leanh::lean_ctor_set(v___x_3120_, 2, v_v_3058_);
                    crate::leanh::lean_ctor_set(v___x_3120_, 1, v_k_3057_);
                    crate::leanh::lean_ctor_set(v___x_3120_, 0, v___x_3115_);
                    v___x_3123_ = v___x_3120_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_k_3057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_v_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___x_3118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_r_3060_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3123_;
            }
            34 => {
                v_k_3145_ = crate::leanh::lean_ctor_get(v_l_3138_, 1);
                v_v_3146_ = crate::leanh::lean_ctor_get(v_l_3138_, 2);
                v_isSharedCheck_3160_ = (!crate::leanh::lean_is_exclusive(v_l_3138_)) as u8;
                if v_isSharedCheck_3160_ == 0 {
                    v_unused_3161_ = crate::leanh::lean_ctor_get(v_l_3138_, 4);
                    crate::leanh::lean_dec(v_unused_3161_);
                    v_unused_3162_ = crate::leanh::lean_ctor_get(v_l_3138_, 3);
                    crate::leanh::lean_dec(v_unused_3162_);
                    v_unused_3163_ = crate::leanh::lean_ctor_get(v_l_3138_, 0);
                    crate::leanh::lean_dec(v_unused_3163_);
                    v___x_3148_ = v_l_3138_;
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3146_);
                    crate::leanh::lean_inc(v_k_3145_);
                    crate::leanh::lean_dec(v_l_3138_);
                    v___x_3148_ = crate::leanh::lean_box(0);
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3150_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_3139_, 2);
                if v_isShared_3149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3148_, 4, v_r_3139_);
                    crate::leanh::lean_ctor_set(v___x_3148_, 3, v_r_3139_);
                    crate::leanh::lean_ctor_set(v___x_3148_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v___x_3148_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v___x_3148_, 0, v___x_3054_);
                    v___x_3152_ = v___x_3148_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_r_3139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_r_3139_);
                    v___x_3152_ = v_reuseFailAlloc_3159_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_3139_);
                if v_isShared_3144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3143_, 3, v_r_3139_);
                    crate::leanh::lean_ctor_set(v___x_3143_, 0, v___x_3054_);
                    v___x_3154_ = v___x_3143_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_k_3140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_v_3141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_r_3139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_r_3139_);
                    v___x_3154_ = v_reuseFailAlloc_3158_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v___x_3154_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v___x_3152_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_3146_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_3145_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3150_);
                    v___x_3156_ = v___x_2910_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_k_3145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_v_3146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 3, v___x_3152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 4, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3156_;
            }
            39 => {
                v___x_3173_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3171_, 4, v_l_3138_);
                    crate::leanh::lean_ctor_set(v___x_3171_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v___x_3171_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3054_);
                    v___x_3175_ = v___x_3171_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_k_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_v_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_l_3138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_l_3138_);
                    v___x_3175_ = v_reuseFailAlloc_3179_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2910_, 4, v_r_3167_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 3, v___x_3175_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 2, v_v_3169_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 1, v_k_3168_);
                    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_3173_);
                    v___x_3177_ = v___x_2910_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_k_3168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_v_3169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 3, v___x_3175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_r_3167_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3177_;
            }
            42 => {
                return v___x_3186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_as_3192_: *mut crate::leanh::LeanObject,
    mut v_i_3193_: usize,
    mut v_stop_3194_: usize,
) -> u8 {
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v___x_3201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3195_ = lean_usize_dec_eq(v_i_3193_, v_stop_3194_);
                if v___x_3195_ == 0 {
                    v___x_3196_ = lean_array_uget_borrowed(v_as_3192_, v_i_3193_);
                    v___x_3197_ = lean_expr_eqv(v_a_3191_, v___x_3196_);
                    if v___x_3197_ == 0 {
                        v___x_3198_ = 1usize;
                        v___x_3199_ = lean_usize_add(v_i_3193_, v___x_3198_);
                        v_i_3193_ = v___x_3199_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3197_;
                    }
                } else {
                    v___x_3201_ = 0;
                    return v___x_3201_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3___boxed(
    mut v_a_3202_: *mut crate::leanh::LeanObject,
    mut v_as_3203_: *mut crate::leanh::LeanObject,
    mut v_i_3204_: *mut crate::leanh::LeanObject,
    mut v_stop_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3206_: usize = 0;
    let mut v_stop_boxed_3207_: usize = 0;
    let mut v_res_3208_: u8 = 0;
    let mut v_r_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3206_ = crate::leanh::lean_unbox_usize(v_i_3204_);
    crate::leanh::lean_dec(v_i_3204_);
    v_stop_boxed_3207_ = crate::leanh::lean_unbox_usize(v_stop_3205_);
    crate::leanh::lean_dec(v_stop_3205_);
    v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_3202_, v_as_3203_, v_i_boxed_3206_, v_stop_boxed_3207_);
    crate::leanh::lean_dec_ref(v_as_3203_);
    crate::leanh::lean_dec_ref(v_a_3202_);
    v_r_3209_ = crate::leanh::lean_box((v_res_3208_) as usize);
    return v_r_3209_;
}
pub unsafe fn l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
    mut v_as_3210_: *mut crate::leanh::LeanObject,
    mut v_a_3211_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    v___x_3212_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3213_ = lean_array_get_size(v_as_3210_);
    v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
    if v___x_3214_ == 0 {
        return v___x_3214_;
    } else {
        if v___x_3214_ == 0 {
            return v___x_3214_;
        } else {
            let mut v___x_3215_: usize = 0;
            let mut v___x_3216_: usize = 0;
            let mut v___x_3217_: u8 = 0;
            v___x_3215_ = 0usize;
            v___x_3216_ = lean_usize_of_nat(v___x_3213_);
            v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_3211_, v_as_3210_, v___x_3215_, v___x_3216_);
            return v___x_3217_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1___boxed(
    mut v_as_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3220_: u8 = 0;
    let mut v_r_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3220_ =
        l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
            v_as_3218_, v_a_3219_,
        );
    crate::leanh::lean_dec_ref(v_a_3219_);
    crate::leanh::lean_dec_ref(v_as_3218_);
    v_r_3221_ = crate::leanh::lean_box((v_res_3220_) as usize);
    return v_r_3221_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
    mut v_ctx_3222_: *mut crate::leanh::LeanObject,
    mut v_i_3223_: *mut crate::leanh::LeanObject,
    mut v_acc_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_i_3223_) == 1 {
        let mut v_i_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: u8 = 0;
        let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_3225_ = crate::leanh::lean_ctor_get(v_i_3223_, 0);
        v_toElabInfo_3226_ = crate::leanh::lean_ctor_get(v_i_3225_, 0);
        v_expr_3227_ = crate::leanh::lean_ctor_get(v_i_3225_, 3);
        v_stx_3228_ = crate::leanh::lean_ctor_get(v_toElabInfo_3226_, 1);
        v___x_3229_ = 1;
        v___x_3230_ = l_Lean_Syntax_getRange_x3f(v_stx_3228_, v___x_3229_);
        if crate::leanh::lean_obj_tag(v___x_3230_) == 1 {
            let mut v_val_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: u8 = 0;
            v_val_3231_ = crate::leanh::lean_ctor_get(v___x_3230_, 0);
            crate::leanh::lean_inc(v_val_3231_);
            crate::leanh::lean_dec_ref_known(v___x_3230_, 1);
            v___x_3232_ = l_Lean_Expr_isFVar(v_expr_3227_);
            if v___x_3232_ == 0 {
                crate::leanh::lean_dec(v_val_3231_);
                return v_acc_3224_;
            } else {
                let mut v_autoImplicits_3233_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_3234_: u8 = 0;
                v_autoImplicits_3233_ = crate::leanh::lean_ctor_get(v_ctx_3222_, 2);
                v___x_3234_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(v_autoImplicits_3233_, v_expr_3227_);
                if v___x_3234_ == 0 {
                    crate::leanh::lean_dec(v_val_3231_);
                    return v_acc_3224_;
                } else {
                    let mut v___x_3235_: u8 = 0;
                    v___x_3235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_val_3231_, v_acc_3224_);
                    if v___x_3235_ == 0 {
                        let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_3236_ = crate::leanh::lean_box(0);
                        v___x_3237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_val_3231_, v___x_3236_, v_acc_3224_);
                        return v___x_3237_;
                    } else {
                        crate::leanh::lean_dec(v_val_3231_);
                        return v_acc_3224_;
                    }
                }
            }
        } else {
            crate::leanh::lean_dec(v___x_3230_);
            return v_acc_3224_;
        }
    } else {
        return v_acc_3224_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(
    mut v_ctx_3238_: *mut crate::leanh::LeanObject,
    mut v_i_3239_: *mut crate::leanh::LeanObject,
    mut v_acc_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
        v_ctx_3238_,
        v_i_3239_,
        v_acc_3240_,
    );
    crate::leanh::lean_dec_ref(v_i_3239_);
    crate::leanh::lean_dec_ref(v_ctx_3238_);
    return v_res_3241_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(
    mut v_x_3242_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    v___x_3243_ = l_Lean_unknownIdentifierMessageTag;
    v___x_3244_ = lean_name_eq(v_x_3242_, v___x_3243_);
    return v___x_3244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed(
    mut v_x_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3246_: u8 = 0;
    let mut v_r_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(v_x_3245_);
    crate::leanh::lean_dec(v_x_3245_);
    v_r_3247_ = crate::leanh::lean_box((v_res_3246_) as usize);
    return v_r_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(
    mut v_text_3249_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3250_: *mut crate::leanh::LeanObject,
    mut v_as_3251_: *mut crate::leanh::LeanObject,
    mut v_sz_3252_: usize,
    mut v_i_3253_: usize,
    mut v_b_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: u8 = 0;
    let mut v_snd_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_a_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: usize = 0;
    let mut v___x_3272_: usize = 0;
    let mut v_reuseFailAlloc_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v_ranges_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut v_unused_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
                if v___x_3256_ == 0 {
                    return v_b_3254_;
                } else {
                    v_snd_3257_ = crate::leanh::lean_ctor_get(v_b_3254_, 1);
                    v_isSharedCheck_3284_ = (!crate::leanh::lean_is_exclusive(v_b_3254_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v_unused_3285_ = crate::leanh::lean_ctor_get(v_b_3254_, 0);
                        crate::leanh::lean_dec(v_unused_3285_);
                        v___x_3259_ = v_b_3254_;
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3257_);
                        crate::leanh::lean_dec(v_b_3254_);
                        v___x_3259_ = crate::leanh::lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3261_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
                v_pos_3262_ = crate::leanh::lean_ctor_get(v_a_3261_, 1);
                v_endPos_3263_ = crate::leanh::lean_ctor_get(v_a_3261_, 2);
                v_data_3264_ = crate::leanh::lean_ctor_get(v_a_3261_, 4);
                v___f_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3266_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3264_);
                v___x_3275_ = l_Lean_MessageData_hasTag(v___f_3265_, v_data_3264_);
                if v___x_3275_ == 0 {
                    v_a_3268_ = v_snd_3257_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3262_);
                    v___x_3276_ = l_Lean_FileMap_ofPosition(v_text_3249_, v_pos_3262_);
                    if crate::leanh::lean_obj_tag(v_endPos_3263_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3262_);
                        v___y_3278_ = v_pos_3262_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3283_ = crate::leanh::lean_ctor_get(v_endPos_3263_, 0);
                        crate::leanh::lean_inc(v_val_3283_);
                        v___y_3278_ = v_val_3283_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_a_3268_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3266_);
                    v___x_3270_ = v___x_3259_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_a_3268_);
                    v___x_3270_ = v_reuseFailAlloc_3274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3271_ = 1usize;
                v___x_3272_ = lean_usize_add(v_i_3253_, v___x_3271_);
                v_i_3253_ = v___x_3272_;
                v_b_3254_ = v___x_3270_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3279_ = l_Lean_FileMap_ofPosition(v_text_3249_, v___y_3278_);
                v_msgRange_3280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3280_, 0, v___x_3276_);
                crate::leanh::lean_ctor_set(v_msgRange_3280_, 1, v___x_3279_);
                v___x_3281_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3280_,
                    v_requestedRange_3250_,
                    v___x_3275_,
                    v___x_3275_,
                );
                if v___x_3281_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_msgRange_3280_, 2);
                    v_a_3268_ = v_snd_3257_;
                    state = 2;
                    continue;
                } else {
                    v_ranges_3282_ = lean_array_push(v_snd_3257_, v_msgRange_3280_);
                    v_a_3268_ = v_ranges_3282_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_text_3286_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3287_: *mut crate::leanh::LeanObject,
    mut v_as_3288_: *mut crate::leanh::LeanObject,
    mut v_sz_3289_: *mut crate::leanh::LeanObject,
    mut v_i_3290_: *mut crate::leanh::LeanObject,
    mut v_b_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3293_: usize = 0;
    let mut v_i_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3293_ = crate::leanh::lean_unbox_usize(v_sz_3289_);
    crate::leanh::lean_dec(v_sz_3289_);
    v_i_boxed_3294_ = crate::leanh::lean_unbox_usize(v_i_3290_);
    crate::leanh::lean_dec(v_i_3290_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_3286_, v_requestedRange_3287_, v_as_3288_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3291_);
    crate::leanh::lean_dec_ref(v_as_3288_);
    crate::leanh::lean_dec_ref(v_requestedRange_3287_);
    crate::leanh::lean_dec_ref(v_text_3286_);
    return v_res_3295_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(
    mut v_text_3296_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3297_: *mut crate::leanh::LeanObject,
    mut v_as_3298_: *mut crate::leanh::LeanObject,
    mut v_sz_3299_: usize,
    mut v_i_3300_: usize,
    mut v_b_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3303_: u8 = 0;
    let mut v_snd_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v_a_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: usize = 0;
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v_ranges_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_unused_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3303_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
                if v___x_3303_ == 0 {
                    return v_b_3301_;
                } else {
                    v_snd_3304_ = crate::leanh::lean_ctor_get(v_b_3301_, 1);
                    v_isSharedCheck_3331_ = (!crate::leanh::lean_is_exclusive(v_b_3301_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v_unused_3332_ = crate::leanh::lean_ctor_get(v_b_3301_, 0);
                        crate::leanh::lean_dec(v_unused_3332_);
                        v___x_3306_ = v_b_3301_;
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3304_);
                        crate::leanh::lean_dec(v_b_3301_);
                        v___x_3306_ = crate::leanh::lean_box(0);
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3308_ = lean_array_uget_borrowed(v_as_3298_, v_i_3300_);
                v_pos_3309_ = crate::leanh::lean_ctor_get(v_a_3308_, 1);
                v_endPos_3310_ = crate::leanh::lean_ctor_get(v_a_3308_, 2);
                v_data_3311_ = crate::leanh::lean_ctor_get(v_a_3308_, 4);
                v___f_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3313_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3311_);
                v___x_3322_ = l_Lean_MessageData_hasTag(v___f_3312_, v_data_3311_);
                if v___x_3322_ == 0 {
                    v_a_3315_ = v_snd_3304_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3309_);
                    v___x_3323_ = l_Lean_FileMap_ofPosition(v_text_3296_, v_pos_3309_);
                    if crate::leanh::lean_obj_tag(v_endPos_3310_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3309_);
                        v___y_3325_ = v_pos_3309_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3330_ = crate::leanh::lean_ctor_get(v_endPos_3310_, 0);
                        crate::leanh::lean_inc(v_val_3330_);
                        v___y_3325_ = v_val_3330_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3307_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3306_, 1, v_a_3315_);
                    crate::leanh::lean_ctor_set(v___x_3306_, 0, v___x_3313_);
                    v___x_3317_ = v___x_3306_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_a_3315_);
                    v___x_3317_ = v_reuseFailAlloc_3321_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3318_ = 1usize;
                v___x_3319_ = lean_usize_add(v_i_3300_, v___x_3318_);
                v___x_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_3296_, v_requestedRange_3297_, v_as_3298_, v_sz_3299_, v___x_3319_, v___x_3317_);
                return v___x_3320_;
            }
            4 => {
                v___x_3326_ = l_Lean_FileMap_ofPosition(v_text_3296_, v___y_3325_);
                v_msgRange_3327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3327_, 0, v___x_3323_);
                crate::leanh::lean_ctor_set(v_msgRange_3327_, 1, v___x_3326_);
                v___x_3328_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3327_,
                    v_requestedRange_3297_,
                    v___x_3322_,
                    v___x_3322_,
                );
                if v___x_3328_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_msgRange_3327_, 2);
                    v_a_3315_ = v_snd_3304_;
                    state = 2;
                    continue;
                } else {
                    v_ranges_3329_ = lean_array_push(v_snd_3304_, v_msgRange_3327_);
                    v_a_3315_ = v_ranges_3329_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2___boxed(
    mut v_text_3333_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3334_: *mut crate::leanh::LeanObject,
    mut v_as_3335_: *mut crate::leanh::LeanObject,
    mut v_sz_3336_: *mut crate::leanh::LeanObject,
    mut v_i_3337_: *mut crate::leanh::LeanObject,
    mut v_b_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3340_: usize = 0;
    let mut v_i_boxed_3341_: usize = 0;
    let mut v_res_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3340_ = crate::leanh::lean_unbox_usize(v_sz_3336_);
    crate::leanh::lean_dec(v_sz_3336_);
    v_i_boxed_3341_ = crate::leanh::lean_unbox_usize(v_i_3337_);
    crate::leanh::lean_dec(v_i_3337_);
    v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3333_, v_requestedRange_3334_, v_as_3335_, v_sz_boxed_3340_, v_i_boxed_3341_, v_b_3338_);
    crate::leanh::lean_dec_ref(v_as_3335_);
    crate::leanh::lean_dec_ref(v_requestedRange_3334_);
    crate::leanh::lean_dec_ref(v_text_3333_);
    return v_res_3342_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(
    mut v_init_3343_: *mut crate::leanh::LeanObject,
    mut v_text_3344_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3345_: *mut crate::leanh::LeanObject,
    mut v_n_3346_: *mut crate::leanh::LeanObject,
    mut v_b_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_n_3346_) == 0 {
        let mut v_cs_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3352_: usize = 0;
        let mut v___x_3353_: usize = 0;
        let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cs_3349_ = crate::leanh::lean_ctor_get(v_n_3346_, 0);
        v___x_3350_ = crate::leanh::lean_box(0);
        v___x_3351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
        crate::leanh::lean_ctor_set(v___x_3351_, 1, v_b_3347_);
        v_sz_3352_ = lean_array_size(v_cs_3349_);
        v___x_3353_ = 0usize;
        v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3343_, v_text_3344_, v_requestedRange_3345_, v_cs_3349_, v_sz_3352_, v___x_3353_, v___x_3351_);
        v_fst_3355_ = crate::leanh::lean_ctor_get(v___x_3354_, 0);
        crate::leanh::lean_inc(v_fst_3355_);
        if crate::leanh::lean_obj_tag(v_fst_3355_) == 0 {
            let mut v_snd_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3356_ = crate::leanh::lean_ctor_get(v___x_3354_, 1);
            crate::leanh::lean_inc(v_snd_3356_);
            crate::leanh::lean_dec_ref(v___x_3354_);
            v___x_3357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3357_, 0, v_snd_3356_);
            return v___x_3357_;
        } else {
            let mut v_val_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3354_);
            v_val_3358_ = crate::leanh::lean_ctor_get(v_fst_3355_, 0);
            crate::leanh::lean_inc(v_val_3358_);
            crate::leanh::lean_dec_ref_known(v_fst_3355_, 1);
            return v_val_3358_;
        }
    } else {
        let mut v_vs_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3362_: usize = 0;
        let mut v___x_3363_: usize = 0;
        let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_3359_ = crate::leanh::lean_ctor_get(v_n_3346_, 0);
        v___x_3360_ = crate::leanh::lean_box(0);
        v___x_3361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3360_);
        crate::leanh::lean_ctor_set(v___x_3361_, 1, v_b_3347_);
        v_sz_3362_ = lean_array_size(v_vs_3359_);
        v___x_3363_ = 0usize;
        v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3344_, v_requestedRange_3345_, v_vs_3359_, v_sz_3362_, v___x_3363_, v___x_3361_);
        v_fst_3365_ = crate::leanh::lean_ctor_get(v___x_3364_, 0);
        crate::leanh::lean_inc(v_fst_3365_);
        if crate::leanh::lean_obj_tag(v_fst_3365_) == 0 {
            let mut v_snd_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3366_ = crate::leanh::lean_ctor_get(v___x_3364_, 1);
            crate::leanh::lean_inc(v_snd_3366_);
            crate::leanh::lean_dec_ref(v___x_3364_);
            v___x_3367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3367_, 0, v_snd_3366_);
            return v___x_3367_;
        } else {
            let mut v_val_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3364_);
            v_val_3368_ = crate::leanh::lean_ctor_get(v_fst_3365_, 0);
            crate::leanh::lean_inc(v_val_3368_);
            crate::leanh::lean_dec_ref_known(v_fst_3365_, 1);
            return v_val_3368_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(
    mut v_init_3369_: *mut crate::leanh::LeanObject,
    mut v_text_3370_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3371_: *mut crate::leanh::LeanObject,
    mut v_as_3372_: *mut crate::leanh::LeanObject,
    mut v_sz_3373_: usize,
    mut v_i_3374_: usize,
    mut v_b_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3377_: u8 = 0;
    let mut v_snd_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: usize = 0;
    let mut v___x_3393_: usize = 0;
    let mut v_reuseFailAlloc_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v_unused_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3377_ = lean_usize_dec_lt(v_i_3374_, v_sz_3373_);
                if v___x_3377_ == 0 {
                    return v_b_3375_;
                } else {
                    v_snd_3378_ = crate::leanh::lean_ctor_get(v_b_3375_, 1);
                    v_isSharedCheck_3396_ = (!crate::leanh::lean_is_exclusive(v_b_3375_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v_unused_3397_ = crate::leanh::lean_ctor_get(v_b_3375_, 0);
                        crate::leanh::lean_dec(v_unused_3397_);
                        v___x_3380_ = v_b_3375_;
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3378_);
                        crate::leanh::lean_dec(v_b_3375_);
                        v___x_3380_ = crate::leanh::lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3382_ = lean_array_uget_borrowed(v_as_3372_, v_i_3374_);
                crate::leanh::lean_inc(v_snd_3378_);
                v___x_3383_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3369_, v_text_3370_, v_requestedRange_3371_, v_a_3382_, v_snd_3378_);
                if crate::leanh::lean_obj_tag(v___x_3383_) == 0 {
                    v___x_3384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3384_, 0, v___x_3383_);
                    if v_isShared_3381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3386_ = v___x_3380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3378_);
                        v___x_3386_ = v_reuseFailAlloc_3387_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3378_);
                    v_a_3388_ = crate::leanh::lean_ctor_get(v___x_3383_, 0);
                    crate::leanh::lean_inc(v_a_3388_);
                    crate::leanh::lean_dec_ref_known(v___x_3383_, 1);
                    v___x_3389_ = crate::leanh::lean_box(0);
                    if v_isShared_3381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3380_, 1, v_a_3388_);
                        crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3380_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3389_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_a_3388_);
                        v___x_3391_ = v_reuseFailAlloc_3395_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3386_;
            }
            3 => {
                v___x_3392_ = 1usize;
                v___x_3393_ = lean_usize_add(v_i_3374_, v___x_3392_);
                v_i_3374_ = v___x_3393_;
                v_b_3375_ = v___x_3391_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(
    mut v_init_3398_: *mut crate::leanh::LeanObject,
    mut v_text_3399_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3400_: *mut crate::leanh::LeanObject,
    mut v_as_3401_: *mut crate::leanh::LeanObject,
    mut v_sz_3402_: *mut crate::leanh::LeanObject,
    mut v_i_3403_: *mut crate::leanh::LeanObject,
    mut v_b_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3406_: usize = 0;
    let mut v_i_boxed_3407_: usize = 0;
    let mut v_res_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3406_ = crate::leanh::lean_unbox_usize(v_sz_3402_);
    crate::leanh::lean_dec(v_sz_3402_);
    v_i_boxed_3407_ = crate::leanh::lean_unbox_usize(v_i_3403_);
    crate::leanh::lean_dec(v_i_3403_);
    v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3398_, v_text_3399_, v_requestedRange_3400_, v_as_3401_, v_sz_boxed_3406_, v_i_boxed_3407_, v_b_3404_);
    crate::leanh::lean_dec_ref(v_as_3401_);
    crate::leanh::lean_dec_ref(v_requestedRange_3400_);
    crate::leanh::lean_dec_ref(v_text_3399_);
    crate::leanh::lean_dec_ref(v_init_3398_);
    return v_res_3408_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(
    mut v_init_3409_: *mut crate::leanh::LeanObject,
    mut v_text_3410_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3411_: *mut crate::leanh::LeanObject,
    mut v_n_3412_: *mut crate::leanh::LeanObject,
    mut v_b_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3409_, v_text_3410_, v_requestedRange_3411_, v_n_3412_, v_b_3413_);
    crate::leanh::lean_dec_ref(v_n_3412_);
    crate::leanh::lean_dec_ref(v_requestedRange_3411_);
    crate::leanh::lean_dec_ref(v_text_3410_);
    crate::leanh::lean_dec_ref(v_init_3409_);
    return v_res_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(
    mut v_text_3416_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3417_: *mut crate::leanh::LeanObject,
    mut v_as_3418_: *mut crate::leanh::LeanObject,
    mut v_sz_3419_: usize,
    mut v_i_3420_: usize,
    mut v_b_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3423_: u8 = 0;
    let mut v_snd_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v_a_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: usize = 0;
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_ranges_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_unused_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3423_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
                if v___x_3423_ == 0 {
                    return v_b_3421_;
                } else {
                    v_snd_3424_ = crate::leanh::lean_ctor_get(v_b_3421_, 1);
                    v_isSharedCheck_3451_ = (!crate::leanh::lean_is_exclusive(v_b_3421_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v_unused_3452_ = crate::leanh::lean_ctor_get(v_b_3421_, 0);
                        crate::leanh::lean_dec(v_unused_3452_);
                        v___x_3426_ = v_b_3421_;
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3424_);
                        crate::leanh::lean_dec(v_b_3421_);
                        v___x_3426_ = crate::leanh::lean_box(0);
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3428_ = lean_array_uget_borrowed(v_as_3418_, v_i_3420_);
                v_pos_3429_ = crate::leanh::lean_ctor_get(v_a_3428_, 1);
                v_endPos_3430_ = crate::leanh::lean_ctor_get(v_a_3428_, 2);
                v_data_3431_ = crate::leanh::lean_ctor_get(v_a_3428_, 4);
                v___f_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3433_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3431_);
                v___x_3442_ = l_Lean_MessageData_hasTag(v___f_3432_, v_data_3431_);
                if v___x_3442_ == 0 {
                    v_a_3435_ = v_snd_3424_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3429_);
                    v___x_3443_ = l_Lean_FileMap_ofPosition(v_text_3416_, v_pos_3429_);
                    if crate::leanh::lean_obj_tag(v_endPos_3430_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3429_);
                        v___y_3445_ = v_pos_3429_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3450_ = crate::leanh::lean_ctor_get(v_endPos_3430_, 0);
                        crate::leanh::lean_inc(v_val_3450_);
                        v___y_3445_ = v_val_3450_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3426_, 1, v_a_3435_);
                    crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3433_);
                    v___x_3437_ = v___x_3426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3435_);
                    v___x_3437_ = v_reuseFailAlloc_3441_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3438_ = 1usize;
                v___x_3439_ = lean_usize_add(v_i_3420_, v___x_3438_);
                v_i_3420_ = v___x_3439_;
                v_b_3421_ = v___x_3437_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3446_ = l_Lean_FileMap_ofPosition(v_text_3416_, v___y_3445_);
                v_msgRange_3447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3447_, 0, v___x_3443_);
                crate::leanh::lean_ctor_set(v_msgRange_3447_, 1, v___x_3446_);
                v___x_3448_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3447_,
                    v_requestedRange_3417_,
                    v___x_3442_,
                    v___x_3442_,
                );
                if v___x_3448_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_msgRange_3447_, 2);
                    v_a_3435_ = v_snd_3424_;
                    state = 2;
                    continue;
                } else {
                    v_ranges_3449_ = lean_array_push(v_snd_3424_, v_msgRange_3447_);
                    v_a_3435_ = v_ranges_3449_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4___boxed(
    mut v_text_3453_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3454_: *mut crate::leanh::LeanObject,
    mut v_as_3455_: *mut crate::leanh::LeanObject,
    mut v_sz_3456_: *mut crate::leanh::LeanObject,
    mut v_i_3457_: *mut crate::leanh::LeanObject,
    mut v_b_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3460_: usize = 0;
    let mut v_i_boxed_3461_: usize = 0;
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3460_ = crate::leanh::lean_unbox_usize(v_sz_3456_);
    crate::leanh::lean_dec(v_sz_3456_);
    v_i_boxed_3461_ = crate::leanh::lean_unbox_usize(v_i_3457_);
    crate::leanh::lean_dec(v_i_3457_);
    v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_3453_, v_requestedRange_3454_, v_as_3455_, v_sz_boxed_3460_, v_i_boxed_3461_, v_b_3458_);
    crate::leanh::lean_dec_ref(v_as_3455_);
    crate::leanh::lean_dec_ref(v_requestedRange_3454_);
    crate::leanh::lean_dec_ref(v_text_3453_);
    return v_res_3462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(
    mut v_text_3463_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3464_: *mut crate::leanh::LeanObject,
    mut v_as_3465_: *mut crate::leanh::LeanObject,
    mut v_sz_3466_: usize,
    mut v_i_3467_: usize,
    mut v_b_3468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3470_: u8 = 0;
    let mut v_snd_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_a_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v_ranges_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v_unused_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
                if v___x_3470_ == 0 {
                    return v_b_3468_;
                } else {
                    v_snd_3471_ = crate::leanh::lean_ctor_get(v_b_3468_, 1);
                    v_isSharedCheck_3498_ = (!crate::leanh::lean_is_exclusive(v_b_3468_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v_unused_3499_ = crate::leanh::lean_ctor_get(v_b_3468_, 0);
                        crate::leanh::lean_dec(v_unused_3499_);
                        v___x_3473_ = v_b_3468_;
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3471_);
                        crate::leanh::lean_dec(v_b_3468_);
                        v___x_3473_ = crate::leanh::lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3475_ = lean_array_uget_borrowed(v_as_3465_, v_i_3467_);
                v_pos_3476_ = crate::leanh::lean_ctor_get(v_a_3475_, 1);
                v_endPos_3477_ = crate::leanh::lean_ctor_get(v_a_3475_, 2);
                v_data_3478_ = crate::leanh::lean_ctor_get(v_a_3475_, 4);
                v___f_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3480_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3478_);
                v___x_3489_ = l_Lean_MessageData_hasTag(v___f_3479_, v_data_3478_);
                if v___x_3489_ == 0 {
                    v_a_3482_ = v_snd_3471_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3476_);
                    v___x_3490_ = l_Lean_FileMap_ofPosition(v_text_3463_, v_pos_3476_);
                    if crate::leanh::lean_obj_tag(v_endPos_3477_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3476_);
                        v___y_3492_ = v_pos_3476_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3497_ = crate::leanh::lean_ctor_get(v_endPos_3477_, 0);
                        crate::leanh::lean_inc(v_val_3497_);
                        v___y_3492_ = v_val_3497_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3473_, 1, v_a_3482_);
                    crate::leanh::lean_ctor_set(v___x_3473_, 0, v___x_3480_);
                    v___x_3484_ = v___x_3473_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_a_3482_);
                    v___x_3484_ = v_reuseFailAlloc_3488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3485_ = 1usize;
                v___x_3486_ = lean_usize_add(v_i_3467_, v___x_3485_);
                v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_3463_, v_requestedRange_3464_, v_as_3465_, v_sz_3466_, v___x_3486_, v___x_3484_);
                return v___x_3487_;
            }
            4 => {
                v___x_3493_ = l_Lean_FileMap_ofPosition(v_text_3463_, v___y_3492_);
                v_msgRange_3494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3494_, 0, v___x_3490_);
                crate::leanh::lean_ctor_set(v_msgRange_3494_, 1, v___x_3493_);
                v___x_3495_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3494_,
                    v_requestedRange_3464_,
                    v___x_3489_,
                    v___x_3489_,
                );
                if v___x_3495_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_msgRange_3494_, 2);
                    v_a_3482_ = v_snd_3471_;
                    state = 2;
                    continue;
                } else {
                    v_ranges_3496_ = lean_array_push(v_snd_3471_, v_msgRange_3494_);
                    v_a_3482_ = v_ranges_3496_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___boxed(
    mut v_text_3500_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3501_: *mut crate::leanh::LeanObject,
    mut v_as_3502_: *mut crate::leanh::LeanObject,
    mut v_sz_3503_: *mut crate::leanh::LeanObject,
    mut v_i_3504_: *mut crate::leanh::LeanObject,
    mut v_b_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3507_: usize = 0;
    let mut v_i_boxed_3508_: usize = 0;
    let mut v_res_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3507_ = crate::leanh::lean_unbox_usize(v_sz_3503_);
    crate::leanh::lean_dec(v_sz_3503_);
    v_i_boxed_3508_ = crate::leanh::lean_unbox_usize(v_i_3504_);
    crate::leanh::lean_dec(v_i_3504_);
    v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3500_, v_requestedRange_3501_, v_as_3502_, v_sz_boxed_3507_, v_i_boxed_3508_, v_b_3505_);
    crate::leanh::lean_dec_ref(v_as_3502_);
    crate::leanh::lean_dec_ref(v_requestedRange_3501_);
    crate::leanh::lean_dec_ref(v_text_3500_);
    return v_res_3509_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(
    mut v_text_3510_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3511_: *mut crate::leanh::LeanObject,
    mut v_t_3512_: *mut crate::leanh::LeanObject,
    mut v_init_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_3515_ = crate::leanh::lean_ctor_get(v_t_3512_, 0);
    v_tail_3516_ = crate::leanh::lean_ctor_get(v_t_3512_, 1);
    crate::leanh::lean_inc_ref(v_init_3513_);
    v___x_3517_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3513_, v_text_3510_, v_requestedRange_3511_, v_root_3515_, v_init_3513_);
    crate::leanh::lean_dec_ref(v_init_3513_);
    if crate::leanh::lean_obj_tag(v___x_3517_) == 0 {
        let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3518_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
        crate::leanh::lean_inc(v_a_3518_);
        crate::leanh::lean_dec_ref_known(v___x_3517_, 1);
        return v_a_3518_;
    } else {
        let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3522_: usize = 0;
        let mut v___x_3523_: usize = 0;
        let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3519_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
        crate::leanh::lean_inc(v_a_3519_);
        crate::leanh::lean_dec_ref_known(v___x_3517_, 1);
        v___x_3520_ = crate::leanh::lean_box(0);
        v___x_3521_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3520_);
        crate::leanh::lean_ctor_set(v___x_3521_, 1, v_a_3519_);
        v_sz_3522_ = lean_array_size(v_tail_3516_);
        v___x_3523_ = 0usize;
        v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3510_, v_requestedRange_3511_, v_tail_3516_, v_sz_3522_, v___x_3523_, v___x_3521_);
        v_fst_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
        crate::leanh::lean_inc(v_fst_3525_);
        if crate::leanh::lean_obj_tag(v_fst_3525_) == 0 {
            let mut v_snd_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3526_ = crate::leanh::lean_ctor_get(v___x_3524_, 1);
            crate::leanh::lean_inc(v_snd_3526_);
            crate::leanh::lean_dec_ref(v___x_3524_);
            return v_snd_3526_;
        } else {
            let mut v_val_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3524_);
            v_val_3527_ = crate::leanh::lean_ctor_get(v_fst_3525_, 0);
            crate::leanh::lean_inc(v_val_3527_);
            crate::leanh::lean_dec_ref_known(v_fst_3525_, 1);
            return v_val_3527_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(
    mut v_text_3528_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3529_: *mut crate::leanh::LeanObject,
    mut v_t_3530_: *mut crate::leanh::LeanObject,
    mut v_init_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3528_, v_requestedRange_3529_, v_t_3530_, v_init_3531_);
    crate::leanh::lean_dec_ref(v_t_3530_);
    crate::leanh::lean_dec_ref(v_requestedRange_3529_);
    crate::leanh::lean_dec_ref(v_text_3528_);
    return v_res_3533_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(
    mut v_init_3534_: *mut crate::leanh::LeanObject,
    mut v_x_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3535_) == 0 {
                    v_k_3536_ = crate::leanh::lean_ctor_get(v_x_3535_, 1);
                    crate::leanh::lean_inc(v_k_3536_);
                    v_l_3537_ = crate::leanh::lean_ctor_get(v_x_3535_, 3);
                    crate::leanh::lean_inc(v_l_3537_);
                    v_r_3538_ = crate::leanh::lean_ctor_get(v_x_3535_, 4);
                    crate::leanh::lean_inc(v_r_3538_);
                    crate::leanh::lean_dec_ref_known(v_x_3535_, 5);
                    v___x_3539_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_3534_, v_l_3537_);
                    v___x_3540_ = lean_array_push(v___x_3539_, v_k_3536_);
                    v_init_3534_ = v___x_3540_;
                    v_x_3535_ = v_r_3538_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3534_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(
    mut v_doc_3549_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: u8 = 0;
    let mut v___y_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_3552_ = crate::leanh::lean_ctor_get(v_doc_3549_, 0);
                crate::leanh::lean_inc_ref(v_toEditableDocumentCore_3552_);
                v_start_3553_ = crate::leanh::lean_ctor_get(v_requestedRange_3550_, 0);
                crate::leanh::lean_inc(v_start_3553_);
                v___x_3554_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_3549_, v_start_3553_);
                v___x_3555_ = lean_task_get_own(v___x_3554_);
                if crate::leanh::lean_obj_tag(v___x_3555_) == 1 {
                    v_meta_3556_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_3552_, 0);
                    crate::leanh::lean_inc_ref(v_meta_3556_);
                    crate::leanh::lean_dec_ref(v_toEditableDocumentCore_3552_);
                    v_val_3557_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                    crate::leanh::lean_inc(v_val_3557_);
                    crate::leanh::lean_dec_ref_known(v___x_3555_, 1);
                    v_text_3558_ = crate::leanh::lean_ctor_get(v_meta_3556_, 3);
                    crate::leanh::lean_inc_ref(v_text_3558_);
                    crate::leanh::lean_dec_ref(v_meta_3556_);
                    v_elabSnap_3559_ = crate::leanh::lean_ctor_get(v_val_3557_, 3);
                    crate::leanh::lean_inc_ref(v_elabSnap_3559_);
                    crate::leanh::lean_dec(v_val_3557_);
                    v_tree_3560_ =
                        l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(
                            v_elabSnap_3559_,
                        );
                    crate::leanh::lean_inc_ref(v_requestedRange_3550_);
                    crate::leanh::lean_inc_ref(v_tree_3560_);
                    v___x_3561_ = l_Lean_Language_SnapshotTree_collectMessagesInRange(
                        v_tree_3560_,
                        v_requestedRange_3550_,
                    );
                    v_msgLog_3562_ = lean_task_get_own(v___x_3561_);
                    v_unreported_3563_ = crate::leanh::lean_ctor_get(v_msgLog_3562_, 1);
                    crate::leanh::lean_inc_ref(v_unreported_3563_);
                    crate::leanh::lean_dec(v_msgLog_3562_);
                    v___x_3564_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_ranges_3565_ =
                        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                    v___x_3566_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3558_, v_requestedRange_3550_, v_unreported_3563_, v_ranges_3565_);
                    crate::leanh::lean_dec_ref(v_unreported_3563_);
                    crate::leanh::lean_dec_ref(v_text_3558_);
                    v___f_3576_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3583_ = lean_array_get_size(v___x_3566_);
                    v___x_3584_ = lean_nat_dec_eq(v___x_3583_, v___x_3564_);
                    if v___x_3584_ == 0 {
                        v___x_3585_ = 1;
                        v___y_3578_ = v___x_3585_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3586_ = 0;
                        v___y_3578_ = v___x_3586_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3555_);
                    crate::leanh::lean_dec_ref(v_toEditableDocumentCore_3552_);
                    crate::leanh::lean_dec_ref(v_requestedRange_3550_);
                    v___x_3587_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2;
                    return v___x_3587_;
                }
            }
            1 => {
                v___x_3571_ = lean_mk_empty_array_with_capacity(v___y_3570_);
                crate::leanh::lean_dec(v___y_3570_);
                v___x_3572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3571_, v___y_3568_);
                v___x_3573_ = l_Array_append___redArg(v___x_3566_, v___x_3572_);
                crate::leanh::lean_dec_ref(v___x_3572_);
                v___x_3574_ = crate::leanh::lean_box((v___y_3569_) as usize);
                v___x_3575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                crate::leanh::lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                return v___x_3575_;
            }
            2 => {
                v___x_3579_ = crate::leanh::lean_box(1);
                v___x_3580_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(
                    v_tree_3560_,
                    v_requestedRange_3550_,
                    v___x_3579_,
                    v___f_3576_,
                );
                v___x_3581_ = lean_task_get_own(v___x_3580_);
                if crate::leanh::lean_obj_tag(v___x_3581_) == 0 {
                    v_size_3582_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                    crate::leanh::lean_inc(v_size_3582_);
                    v___y_3568_ = v___x_3581_;
                    v___y_3569_ = v___y_3578_;
                    v___y_3570_ = v_size_3582_;
                    state = 1;
                    continue;
                } else {
                    v___y_3568_ = v___x_3581_;
                    v___y_3569_ = v___y_3578_;
                    v___y_3570_ = v___x_3564_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___boxed(
    mut v_doc_3588_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ =
        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(v_doc_3588_, v_requestedRange_3589_);
    return v_res_3591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(
    mut v_00_u03b2_3592_: *mut crate::leanh::LeanObject,
    mut v_k_3593_: *mut crate::leanh::LeanObject,
    mut v_t_3594_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3595_: u8 = 0;
    v___x_3595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_3593_, v_t_3594_);
    return v___x_3595_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(
    mut v_00_u03b2_3596_: *mut crate::leanh::LeanObject,
    mut v_k_3597_: *mut crate::leanh::LeanObject,
    mut v_t_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3599_: u8 = 0;
    let mut v_r_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_00_u03b2_3596_, v_k_3597_, v_t_3598_);
    crate::leanh::lean_dec(v_t_3598_);
    crate::leanh::lean_dec_ref(v_k_3597_);
    v_r_3600_ = crate::leanh::lean_box((v_res_3599_) as usize);
    return v_r_3600_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(
    mut v_00_u03b2_3601_: *mut crate::leanh::LeanObject,
    mut v_k_3602_: *mut crate::leanh::LeanObject,
    mut v_v_3603_: *mut crate::leanh::LeanObject,
    mut v_t_3604_: *mut crate::leanh::LeanObject,
    mut v_hl_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_3602_, v_v_3603_, v_t_3604_);
    return v___x_3606_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(
    mut v_init_3607_: *mut crate::leanh::LeanObject,
    mut v_t_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_3607_, v_t_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(
    mut v_s_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ =
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0;
    v___x_3614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3614_, 0, v_s_3612_);
    crate::leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(
    mut v___f_3616_: *mut crate::leanh::LeanObject,
    mut v_s_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSnapshot_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v_firstCmdSnap_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_3618_ = crate::leanh::lean_ctor_get(v_s_3617_, 0);
                crate::leanh::lean_inc_ref(v_toSnapshot_3618_);
                v_metaSnap_3619_ = crate::leanh::lean_ctor_get(v_s_3617_, 1);
                crate::leanh::lean_inc_ref(v_metaSnap_3619_);
                v_result_x3f_3620_ = crate::leanh::lean_ctor_get(v_s_3617_, 2);
                crate::leanh::lean_inc(v_result_x3f_3620_);
                crate::leanh::lean_dec_ref(v_s_3617_);
                if crate::leanh::lean_obj_tag(v_result_x3f_3620_) == 0 {
                    v___x_3632_ = crate::leanh::lean_box(0);
                    v___y_3622_ = v___x_3632_;
                    state = 1;
                    continue;
                } else {
                    v_val_3633_ = crate::leanh::lean_ctor_get(v_result_x3f_3620_, 0);
                    v_isSharedCheck_3646_ =
                        (!crate::leanh::lean_is_exclusive(v_result_x3f_3620_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3635_ = v_result_x3f_3620_;
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3633_);
                        crate::leanh::lean_dec(v_result_x3f_3620_);
                        v___x_3635_ = crate::leanh::lean_box(0);
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_3623_ = crate::leanh::lean_ctor_get(v_metaSnap_3619_, 0);
                crate::leanh::lean_inc(v_stx_x3f_3623_);
                v_reportingRange_3624_ = crate::leanh::lean_ctor_get(v_metaSnap_3619_, 1);
                crate::leanh::lean_inc(v_reportingRange_3624_);
                v___x_3625_ = 1;
                v___x_3626_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_3619_,
                    v___f_3616_,
                    v_stx_x3f_3623_,
                    v_reportingRange_3624_,
                    v___x_3625_,
                );
                v___x_3627_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
                v___x_3629_ = lean_array_push(v___x_3628_, v___x_3626_);
                v___x_3630_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_3622_, v___x_3629_);
                v___x_3631_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3631_, 0, v_toSnapshot_3618_);
                crate::leanh::lean_ctor_set(v___x_3631_, 1, v___x_3630_);
                return v___x_3631_;
            }
            2 => {
                v_firstCmdSnap_3637_ = crate::leanh::lean_ctor_get(v_val_3633_, 1);
                crate::leanh::lean_inc_ref(v_firstCmdSnap_3637_);
                crate::leanh::lean_dec(v_val_3633_);
                v_stx_x3f_3638_ = crate::leanh::lean_ctor_get(v_firstCmdSnap_3637_, 0);
                crate::leanh::lean_inc(v_stx_x3f_3638_);
                v_reportingRange_3639_ = crate::leanh::lean_ctor_get(v_firstCmdSnap_3637_, 1);
                crate::leanh::lean_inc(v_reportingRange_3639_);
                v___x_3640_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0;
                v___x_3641_ = 1;
                v___x_3642_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_firstCmdSnap_3637_,
                    v___x_3640_,
                    v_stx_x3f_3638_,
                    v_reportingRange_3639_,
                    v___x_3641_,
                );
                if v_isShared_3636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3635_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3622_ = v___x_3644_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(
    mut v_as_3647_: *mut crate::leanh::LeanObject,
    mut v_i_3648_: usize,
    mut v_stop_3649_: usize,
    mut v_b_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3651_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = lean_usize_dec_eq(v_i_3648_, v_stop_3649_);
                if v___x_3651_ == 0 {
                    v___x_3652_ = lean_array_uget_borrowed(v_as_3647_, v_i_3648_);
                    crate::leanh::lean_inc(v___x_3652_);
                    v___x_3653_ = l_Lean_MessageLog_append(v_b_3650_, v___x_3652_);
                    v___x_3654_ = 1usize;
                    v___x_3655_ = lean_usize_add(v_i_3648_, v___x_3654_);
                    v_i_3648_ = v___x_3655_;
                    v_b_3650_ = v___x_3653_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3650_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3___boxed(
    mut v_as_3657_: *mut crate::leanh::LeanObject,
    mut v_i_3658_: *mut crate::leanh::LeanObject,
    mut v_stop_3659_: *mut crate::leanh::LeanObject,
    mut v_b_3660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3661_: usize = 0;
    let mut v_stop_boxed_3662_: usize = 0;
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3661_ = crate::leanh::lean_unbox_usize(v_i_3658_);
    crate::leanh::lean_dec(v_i_3658_);
    v_stop_boxed_3662_ = crate::leanh::lean_unbox_usize(v_stop_3659_);
    crate::leanh::lean_dec(v_stop_3659_);
    v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v_as_3657_, v_i_boxed_3661_, v_stop_boxed_3662_, v_b_3660_);
    crate::leanh::lean_dec_ref(v_as_3657_);
    return v_res_3663_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(
    mut v_as_x27_3664_: *mut crate::leanh::LeanObject,
    mut v_b_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3664_) == 0 {
                    return v_b_3665_;
                } else {
                    v_head_3667_ = crate::leanh::lean_ctor_get(v_as_x27_3664_, 0);
                    v_tail_3668_ = crate::leanh::lean_ctor_get(v_as_x27_3664_, 1);
                    v___f_3669_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3670_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v_head_3667_);
                    v___x_3671_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3667_);
                    v___x_3672_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3669_,
                        v___x_3670_,
                        v___x_3671_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3672_) == 0 {
                        v_size_3679_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                        crate::leanh::lean_inc(v_size_3679_);
                        v___y_3674_ = v_size_3679_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3680_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_3674_ = v___x_3680_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3675_ = lean_mk_empty_array_with_capacity(v___y_3674_);
                crate::leanh::lean_dec(v___y_3674_);
                v___x_3676_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3675_, v___x_3672_);
                v___x_3677_ = l_Array_append___redArg(v_b_3665_, v___x_3676_);
                crate::leanh::lean_dec_ref(v___x_3676_);
                v_as_x27_3664_ = v_tail_3668_;
                v_b_3665_ = v___x_3677_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg___boxed(
    mut v_as_x27_3681_: *mut crate::leanh::LeanObject,
    mut v_b_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_3681_, v_b_3682_);
    crate::leanh::lean_dec(v_as_x27_3681_);
    return v_res_3684_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(
    mut v_as_3685_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3686_: *mut crate::leanh::LeanObject,
    mut v_b_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3686_) == 0 {
                    return v_b_3687_;
                } else {
                    v_head_3689_ = crate::leanh::lean_ctor_get(v_as_x27_3686_, 0);
                    v_tail_3690_ = crate::leanh::lean_ctor_get(v_as_x27_3686_, 1);
                    v___f_3691_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3692_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v_head_3689_);
                    v___x_3693_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3689_);
                    v___x_3694_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3691_,
                        v___x_3692_,
                        v___x_3693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_size_3701_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                        crate::leanh::lean_inc(v_size_3701_);
                        v___y_3696_ = v_size_3701_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3702_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_3696_ = v___x_3702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3697_ = lean_mk_empty_array_with_capacity(v___y_3696_);
                crate::leanh::lean_dec(v___y_3696_);
                v___x_3698_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3697_, v___x_3694_);
                v___x_3699_ = l_Array_append___redArg(v_b_3687_, v___x_3698_);
                crate::leanh::lean_dec_ref(v___x_3698_);
                v___x_3700_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_tail_3690_, v___x_3699_);
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(
    mut v_as_3703_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3704_: *mut crate::leanh::LeanObject,
    mut v_b_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_3703_, v_as_x27_3704_, v_b_3705_);
    crate::leanh::lean_dec(v_as_x27_3704_);
    crate::leanh::lean_dec(v_as_3703_);
    return v_res_3707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(
    mut v_text_3708_: *mut crate::leanh::LeanObject,
    mut v_as_3709_: *mut crate::leanh::LeanObject,
    mut v_sz_3710_: usize,
    mut v_i_3711_: usize,
    mut v_b_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: u8 = 0;
    let mut v_snd_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v_a_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: usize = 0;
    let mut v_reuseFailAlloc_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_unused_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3714_ = lean_usize_dec_lt(v_i_3711_, v_sz_3710_);
                if v___x_3714_ == 0 {
                    return v_b_3712_;
                } else {
                    v_snd_3715_ = crate::leanh::lean_ctor_get(v_b_3712_, 1);
                    v_isSharedCheck_3741_ = (!crate::leanh::lean_is_exclusive(v_b_3712_)) as u8;
                    if v_isSharedCheck_3741_ == 0 {
                        v_unused_3742_ = crate::leanh::lean_ctor_get(v_b_3712_, 0);
                        crate::leanh::lean_dec(v_unused_3742_);
                        v___x_3717_ = v_b_3712_;
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3715_);
                        crate::leanh::lean_dec(v_b_3712_);
                        v___x_3717_ = crate::leanh::lean_box(0);
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3719_ = lean_array_uget_borrowed(v_as_3709_, v_i_3711_);
                v_pos_3720_ = crate::leanh::lean_ctor_get(v_a_3719_, 1);
                v_endPos_3721_ = crate::leanh::lean_ctor_get(v_a_3719_, 2);
                v_data_3722_ = crate::leanh::lean_ctor_get(v_a_3719_, 4);
                v___f_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3724_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3722_);
                v___x_3733_ = l_Lean_MessageData_hasTag(v___f_3723_, v_data_3722_);
                if v___x_3733_ == 0 {
                    v_a_3726_ = v_snd_3715_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3720_);
                    v___x_3734_ = l_Lean_FileMap_ofPosition(v_text_3708_, v_pos_3720_);
                    if crate::leanh::lean_obj_tag(v_endPos_3721_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3720_);
                        v___y_3736_ = v_pos_3720_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3740_ = crate::leanh::lean_ctor_get(v_endPos_3721_, 0);
                        crate::leanh::lean_inc(v_val_3740_);
                        v___y_3736_ = v_val_3740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_a_3726_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v___x_3724_);
                    v___x_3728_ = v___x_3717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_a_3726_);
                    v___x_3728_ = v_reuseFailAlloc_3732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3729_ = 1usize;
                v___x_3730_ = lean_usize_add(v_i_3711_, v___x_3729_);
                v_i_3711_ = v___x_3730_;
                v_b_3712_ = v___x_3728_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3737_ = l_Lean_FileMap_ofPosition(v_text_3708_, v___y_3736_);
                v_msgRange_3738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3738_, 0, v___x_3734_);
                crate::leanh::lean_ctor_set(v_msgRange_3738_, 1, v___x_3737_);
                v_ranges_3739_ = lean_array_push(v_snd_3715_, v_msgRange_3738_);
                v_a_3726_ = v_ranges_3739_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4___boxed(
    mut v_text_3743_: *mut crate::leanh::LeanObject,
    mut v_as_3744_: *mut crate::leanh::LeanObject,
    mut v_sz_3745_: *mut crate::leanh::LeanObject,
    mut v_i_3746_: *mut crate::leanh::LeanObject,
    mut v_b_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3749_: usize = 0;
    let mut v_i_boxed_3750_: usize = 0;
    let mut v_res_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3749_ = crate::leanh::lean_unbox_usize(v_sz_3745_);
    crate::leanh::lean_dec(v_sz_3745_);
    v_i_boxed_3750_ = crate::leanh::lean_unbox_usize(v_i_3746_);
    crate::leanh::lean_dec(v_i_3746_);
    v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_3743_, v_as_3744_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3747_);
    crate::leanh::lean_dec_ref(v_as_3744_);
    crate::leanh::lean_dec_ref(v_text_3743_);
    return v_res_3751_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(
    mut v_text_3752_: *mut crate::leanh::LeanObject,
    mut v_as_3753_: *mut crate::leanh::LeanObject,
    mut v_sz_3754_: usize,
    mut v_i_3755_: usize,
    mut v_b_3756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: u8 = 0;
    let mut v_snd_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: usize = 0;
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
                if v___x_3758_ == 0 {
                    return v_b_3756_;
                } else {
                    v_snd_3759_ = crate::leanh::lean_ctor_get(v_b_3756_, 1);
                    v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v_b_3756_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v_unused_3786_ = crate::leanh::lean_ctor_get(v_b_3756_, 0);
                        crate::leanh::lean_dec(v_unused_3786_);
                        v___x_3761_ = v_b_3756_;
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3759_);
                        crate::leanh::lean_dec(v_b_3756_);
                        v___x_3761_ = crate::leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3763_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
                v_pos_3764_ = crate::leanh::lean_ctor_get(v_a_3763_, 1);
                v_endPos_3765_ = crate::leanh::lean_ctor_get(v_a_3763_, 2);
                v_data_3766_ = crate::leanh::lean_ctor_get(v_a_3763_, 4);
                v___f_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3768_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3766_);
                v___x_3777_ = l_Lean_MessageData_hasTag(v___f_3767_, v_data_3766_);
                if v___x_3777_ == 0 {
                    v_a_3770_ = v_snd_3759_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3764_);
                    v___x_3778_ = l_Lean_FileMap_ofPosition(v_text_3752_, v_pos_3764_);
                    if crate::leanh::lean_obj_tag(v_endPos_3765_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3764_);
                        v___y_3780_ = v_pos_3764_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3784_ = crate::leanh::lean_ctor_get(v_endPos_3765_, 0);
                        crate::leanh::lean_inc(v_val_3784_);
                        v___y_3780_ = v_val_3784_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3761_, 1, v_a_3770_);
                    crate::leanh::lean_ctor_set(v___x_3761_, 0, v___x_3768_);
                    v___x_3772_ = v___x_3761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_a_3770_);
                    v___x_3772_ = v_reuseFailAlloc_3776_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3773_ = 1usize;
                v___x_3774_ = lean_usize_add(v_i_3755_, v___x_3773_);
                v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_3752_, v_as_3753_, v_sz_3754_, v___x_3774_, v___x_3772_);
                return v___x_3775_;
            }
            4 => {
                v___x_3781_ = l_Lean_FileMap_ofPosition(v_text_3752_, v___y_3780_);
                v_msgRange_3782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3782_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v_msgRange_3782_, 1, v___x_3781_);
                v_ranges_3783_ = lean_array_push(v_snd_3759_, v_msgRange_3782_);
                v_a_3770_ = v_ranges_3783_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1___boxed(
    mut v_text_3787_: *mut crate::leanh::LeanObject,
    mut v_as_3788_: *mut crate::leanh::LeanObject,
    mut v_sz_3789_: *mut crate::leanh::LeanObject,
    mut v_i_3790_: *mut crate::leanh::LeanObject,
    mut v_b_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3793_: usize = 0;
    let mut v_i_boxed_3794_: usize = 0;
    let mut v_res_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3793_ = crate::leanh::lean_unbox_usize(v_sz_3789_);
    crate::leanh::lean_dec(v_sz_3789_);
    v_i_boxed_3794_ = crate::leanh::lean_unbox_usize(v_i_3790_);
    crate::leanh::lean_dec(v_i_3790_);
    v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3787_, v_as_3788_, v_sz_boxed_3793_, v_i_boxed_3794_, v_b_3791_);
    crate::leanh::lean_dec_ref(v_as_3788_);
    crate::leanh::lean_dec_ref(v_text_3787_);
    return v_res_3795_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(
    mut v_text_3796_: *mut crate::leanh::LeanObject,
    mut v_as_3797_: *mut crate::leanh::LeanObject,
    mut v_sz_3798_: usize,
    mut v_i_3799_: usize,
    mut v_b_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: u8 = 0;
    let mut v_snd_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: usize = 0;
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_unused_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
                if v___x_3802_ == 0 {
                    return v_b_3800_;
                } else {
                    v_snd_3803_ = crate::leanh::lean_ctor_get(v_b_3800_, 1);
                    v_isSharedCheck_3829_ = (!crate::leanh::lean_is_exclusive(v_b_3800_)) as u8;
                    if v_isSharedCheck_3829_ == 0 {
                        v_unused_3830_ = crate::leanh::lean_ctor_get(v_b_3800_, 0);
                        crate::leanh::lean_dec(v_unused_3830_);
                        v___x_3805_ = v_b_3800_;
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3803_);
                        crate::leanh::lean_dec(v_b_3800_);
                        v___x_3805_ = crate::leanh::lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3807_ = lean_array_uget_borrowed(v_as_3797_, v_i_3799_);
                v_pos_3808_ = crate::leanh::lean_ctor_get(v_a_3807_, 1);
                v_endPos_3809_ = crate::leanh::lean_ctor_get(v_a_3807_, 2);
                v_data_3810_ = crate::leanh::lean_ctor_get(v_a_3807_, 4);
                v___f_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3812_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3810_);
                v___x_3821_ = l_Lean_MessageData_hasTag(v___f_3811_, v_data_3810_);
                if v___x_3821_ == 0 {
                    v_a_3814_ = v_snd_3803_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3808_);
                    v___x_3822_ = l_Lean_FileMap_ofPosition(v_text_3796_, v_pos_3808_);
                    if crate::leanh::lean_obj_tag(v_endPos_3809_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3808_);
                        v___y_3824_ = v_pos_3808_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3828_ = crate::leanh::lean_ctor_get(v_endPos_3809_, 0);
                        crate::leanh::lean_inc(v_val_3828_);
                        v___y_3824_ = v_val_3828_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3805_, 1, v_a_3814_);
                    crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3812_);
                    v___x_3816_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3814_);
                    v___x_3816_ = v_reuseFailAlloc_3820_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3817_ = 1usize;
                v___x_3818_ = lean_usize_add(v_i_3799_, v___x_3817_);
                v_i_3799_ = v___x_3818_;
                v_b_3800_ = v___x_3816_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3825_ = l_Lean_FileMap_ofPosition(v_text_3796_, v___y_3824_);
                v_msgRange_3826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3826_, 0, v___x_3822_);
                crate::leanh::lean_ctor_set(v_msgRange_3826_, 1, v___x_3825_);
                v_ranges_3827_ = lean_array_push(v_snd_3803_, v_msgRange_3826_);
                v_a_3814_ = v_ranges_3827_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_text_3831_: *mut crate::leanh::LeanObject,
    mut v_as_3832_: *mut crate::leanh::LeanObject,
    mut v_sz_3833_: *mut crate::leanh::LeanObject,
    mut v_i_3834_: *mut crate::leanh::LeanObject,
    mut v_b_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3837_: usize = 0;
    let mut v_i_boxed_3838_: usize = 0;
    let mut v_res_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3837_ = crate::leanh::lean_unbox_usize(v_sz_3833_);
    crate::leanh::lean_dec(v_sz_3833_);
    v_i_boxed_3838_ = crate::leanh::lean_unbox_usize(v_i_3834_);
    crate::leanh::lean_dec(v_i_3834_);
    v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_3831_, v_as_3832_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3835_);
    crate::leanh::lean_dec_ref(v_as_3832_);
    crate::leanh::lean_dec_ref(v_text_3831_);
    return v_res_3839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(
    mut v_text_3840_: *mut crate::leanh::LeanObject,
    mut v_as_3841_: *mut crate::leanh::LeanObject,
    mut v_sz_3842_: usize,
    mut v_i_3843_: usize,
    mut v_b_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3846_: u8 = 0;
    let mut v_snd_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v_a_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: usize = 0;
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_unused_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3846_ = lean_usize_dec_lt(v_i_3843_, v_sz_3842_);
                if v___x_3846_ == 0 {
                    return v_b_3844_;
                } else {
                    v_snd_3847_ = crate::leanh::lean_ctor_get(v_b_3844_, 1);
                    v_isSharedCheck_3873_ = (!crate::leanh::lean_is_exclusive(v_b_3844_)) as u8;
                    if v_isSharedCheck_3873_ == 0 {
                        v_unused_3874_ = crate::leanh::lean_ctor_get(v_b_3844_, 0);
                        crate::leanh::lean_dec(v_unused_3874_);
                        v___x_3849_ = v_b_3844_;
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3847_);
                        crate::leanh::lean_dec(v_b_3844_);
                        v___x_3849_ = crate::leanh::lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3851_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
                v_pos_3852_ = crate::leanh::lean_ctor_get(v_a_3851_, 1);
                v_endPos_3853_ = crate::leanh::lean_ctor_get(v_a_3851_, 2);
                v_data_3854_ = crate::leanh::lean_ctor_get(v_a_3851_, 4);
                v___f_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3856_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_data_3854_);
                v___x_3865_ = l_Lean_MessageData_hasTag(v___f_3855_, v_data_3854_);
                if v___x_3865_ == 0 {
                    v_a_3858_ = v_snd_3847_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_pos_3852_);
                    v___x_3866_ = l_Lean_FileMap_ofPosition(v_text_3840_, v_pos_3852_);
                    if crate::leanh::lean_obj_tag(v_endPos_3853_) == 0 {
                        crate::leanh::lean_inc_ref(v_pos_3852_);
                        v___y_3868_ = v_pos_3852_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3872_ = crate::leanh::lean_ctor_get(v_endPos_3853_, 0);
                        crate::leanh::lean_inc(v_val_3872_);
                        v___y_3868_ = v_val_3872_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3849_, 1, v_a_3858_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3856_);
                    v___x_3860_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_a_3858_);
                    v___x_3860_ = v_reuseFailAlloc_3864_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3861_ = 1usize;
                v___x_3862_ = lean_usize_add(v_i_3843_, v___x_3861_);
                v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_3840_, v_as_3841_, v_sz_3842_, v___x_3862_, v___x_3860_);
                return v___x_3863_;
            }
            4 => {
                v___x_3869_ = l_Lean_FileMap_ofPosition(v_text_3840_, v___y_3868_);
                v_msgRange_3870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgRange_3870_, 0, v___x_3866_);
                crate::leanh::lean_ctor_set(v_msgRange_3870_, 1, v___x_3869_);
                v_ranges_3871_ = lean_array_push(v_snd_3847_, v_msgRange_3870_);
                v_a_3858_ = v_ranges_3871_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2___boxed(
    mut v_text_3875_: *mut crate::leanh::LeanObject,
    mut v_as_3876_: *mut crate::leanh::LeanObject,
    mut v_sz_3877_: *mut crate::leanh::LeanObject,
    mut v_i_3878_: *mut crate::leanh::LeanObject,
    mut v_b_3879_: *mut crate::leanh::LeanObject,
    mut v___y_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3881_: usize = 0;
    let mut v_i_boxed_3882_: usize = 0;
    let mut v_res_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3881_ = crate::leanh::lean_unbox_usize(v_sz_3877_);
    crate::leanh::lean_dec(v_sz_3877_);
    v_i_boxed_3882_ = crate::leanh::lean_unbox_usize(v_i_3878_);
    crate::leanh::lean_dec(v_i_3878_);
    v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3875_, v_as_3876_, v_sz_boxed_3881_, v_i_boxed_3882_, v_b_3879_);
    crate::leanh::lean_dec_ref(v_as_3876_);
    crate::leanh::lean_dec_ref(v_text_3875_);
    return v_res_3883_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(
    mut v_init_3884_: *mut crate::leanh::LeanObject,
    mut v_text_3885_: *mut crate::leanh::LeanObject,
    mut v_n_3886_: *mut crate::leanh::LeanObject,
    mut v_b_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_n_3886_) == 0 {
        let mut v_cs_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3892_: usize = 0;
        let mut v___x_3893_: usize = 0;
        let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cs_3889_ = crate::leanh::lean_ctor_get(v_n_3886_, 0);
        v___x_3890_ = crate::leanh::lean_box(0);
        v___x_3891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3890_);
        crate::leanh::lean_ctor_set(v___x_3891_, 1, v_b_3887_);
        v_sz_3892_ = lean_array_size(v_cs_3889_);
        v___x_3893_ = 0usize;
        v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3884_, v_text_3885_, v_cs_3889_, v_sz_3892_, v___x_3893_, v___x_3891_);
        v_fst_3895_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
        crate::leanh::lean_inc(v_fst_3895_);
        if crate::leanh::lean_obj_tag(v_fst_3895_) == 0 {
            let mut v_snd_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3896_ = crate::leanh::lean_ctor_get(v___x_3894_, 1);
            crate::leanh::lean_inc(v_snd_3896_);
            crate::leanh::lean_dec_ref(v___x_3894_);
            v___x_3897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3897_, 0, v_snd_3896_);
            return v___x_3897_;
        } else {
            let mut v_val_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3894_);
            v_val_3898_ = crate::leanh::lean_ctor_get(v_fst_3895_, 0);
            crate::leanh::lean_inc(v_val_3898_);
            crate::leanh::lean_dec_ref_known(v_fst_3895_, 1);
            return v_val_3898_;
        }
    } else {
        let mut v_vs_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3902_: usize = 0;
        let mut v___x_3903_: usize = 0;
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_3899_ = crate::leanh::lean_ctor_get(v_n_3886_, 0);
        v___x_3900_ = crate::leanh::lean_box(0);
        v___x_3901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3901_, 0, v___x_3900_);
        crate::leanh::lean_ctor_set(v___x_3901_, 1, v_b_3887_);
        v_sz_3902_ = lean_array_size(v_vs_3899_);
        v___x_3903_ = 0usize;
        v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3885_, v_vs_3899_, v_sz_3902_, v___x_3903_, v___x_3901_);
        v_fst_3905_ = crate::leanh::lean_ctor_get(v___x_3904_, 0);
        crate::leanh::lean_inc(v_fst_3905_);
        if crate::leanh::lean_obj_tag(v_fst_3905_) == 0 {
            let mut v_snd_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3906_ = crate::leanh::lean_ctor_get(v___x_3904_, 1);
            crate::leanh::lean_inc(v_snd_3906_);
            crate::leanh::lean_dec_ref(v___x_3904_);
            v___x_3907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3907_, 0, v_snd_3906_);
            return v___x_3907_;
        } else {
            let mut v_val_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3904_);
            v_val_3908_ = crate::leanh::lean_ctor_get(v_fst_3905_, 0);
            crate::leanh::lean_inc(v_val_3908_);
            crate::leanh::lean_dec_ref_known(v_fst_3905_, 1);
            return v_val_3908_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(
    mut v_init_3909_: *mut crate::leanh::LeanObject,
    mut v_text_3910_: *mut crate::leanh::LeanObject,
    mut v_as_3911_: *mut crate::leanh::LeanObject,
    mut v_sz_3912_: usize,
    mut v_i_3913_: usize,
    mut v_b_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: u8 = 0;
    let mut v_snd_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: usize = 0;
    let mut v___x_3932_: usize = 0;
    let mut v_reuseFailAlloc_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = lean_usize_dec_lt(v_i_3913_, v_sz_3912_);
                if v___x_3916_ == 0 {
                    return v_b_3914_;
                } else {
                    v_snd_3917_ = crate::leanh::lean_ctor_get(v_b_3914_, 1);
                    v_isSharedCheck_3935_ = (!crate::leanh::lean_is_exclusive(v_b_3914_)) as u8;
                    if v_isSharedCheck_3935_ == 0 {
                        v_unused_3936_ = crate::leanh::lean_ctor_get(v_b_3914_, 0);
                        crate::leanh::lean_dec(v_unused_3936_);
                        v___x_3919_ = v_b_3914_;
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3917_);
                        crate::leanh::lean_dec(v_b_3914_);
                        v___x_3919_ = crate::leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3921_ = lean_array_uget_borrowed(v_as_3911_, v_i_3913_);
                crate::leanh::lean_inc(v_snd_3917_);
                v___x_3922_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3909_, v_text_3910_, v_a_3921_, v_snd_3917_);
                if crate::leanh::lean_obj_tag(v___x_3922_) == 0 {
                    v___x_3923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                    if v_isShared_3920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3917_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3917_);
                    v_a_3927_ = crate::leanh::lean_ctor_get(v___x_3922_, 0);
                    crate::leanh::lean_inc(v_a_3927_);
                    crate::leanh::lean_dec_ref_known(v___x_3922_, 1);
                    v___x_3928_ = crate::leanh::lean_box(0);
                    if v_isShared_3920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3919_, 1, v_a_3927_);
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3928_);
                        v___x_3930_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_a_3927_);
                        v___x_3930_ = v_reuseFailAlloc_3934_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3925_;
            }
            3 => {
                v___x_3931_ = 1usize;
                v___x_3932_ = lean_usize_add(v_i_3913_, v___x_3931_);
                v_i_3913_ = v___x_3932_;
                v_b_3914_ = v___x_3930_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1___boxed(
    mut v_init_3937_: *mut crate::leanh::LeanObject,
    mut v_text_3938_: *mut crate::leanh::LeanObject,
    mut v_as_3939_: *mut crate::leanh::LeanObject,
    mut v_sz_3940_: *mut crate::leanh::LeanObject,
    mut v_i_3941_: *mut crate::leanh::LeanObject,
    mut v_b_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3944_: usize = 0;
    let mut v_i_boxed_3945_: usize = 0;
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3944_ = crate::leanh::lean_unbox_usize(v_sz_3940_);
    crate::leanh::lean_dec(v_sz_3940_);
    v_i_boxed_3945_ = crate::leanh::lean_unbox_usize(v_i_3941_);
    crate::leanh::lean_dec(v_i_3941_);
    v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3937_, v_text_3938_, v_as_3939_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3942_);
    crate::leanh::lean_dec_ref(v_as_3939_);
    crate::leanh::lean_dec_ref(v_text_3938_);
    crate::leanh::lean_dec_ref(v_init_3937_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(
    mut v_init_3947_: *mut crate::leanh::LeanObject,
    mut v_text_3948_: *mut crate::leanh::LeanObject,
    mut v_n_3949_: *mut crate::leanh::LeanObject,
    mut v_b_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3947_, v_text_3948_, v_n_3949_, v_b_3950_);
    crate::leanh::lean_dec_ref(v_n_3949_);
    crate::leanh::lean_dec_ref(v_text_3948_);
    crate::leanh::lean_dec_ref(v_init_3947_);
    return v_res_3952_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(
    mut v_text_3953_: *mut crate::leanh::LeanObject,
    mut v_t_3954_: *mut crate::leanh::LeanObject,
    mut v_init_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_3957_ = crate::leanh::lean_ctor_get(v_t_3954_, 0);
    v_tail_3958_ = crate::leanh::lean_ctor_get(v_t_3954_, 1);
    crate::leanh::lean_inc_ref(v_init_3955_);
    v___x_3959_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3955_, v_text_3953_, v_root_3957_, v_init_3955_);
    crate::leanh::lean_dec_ref(v_init_3955_);
    if crate::leanh::lean_obj_tag(v___x_3959_) == 0 {
        let mut v_a_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3960_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
        crate::leanh::lean_inc(v_a_3960_);
        crate::leanh::lean_dec_ref_known(v___x_3959_, 1);
        return v_a_3960_;
    } else {
        let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3964_: usize = 0;
        let mut v___x_3965_: usize = 0;
        let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
        crate::leanh::lean_inc(v_a_3961_);
        crate::leanh::lean_dec_ref_known(v___x_3959_, 1);
        v___x_3962_ = crate::leanh::lean_box(0);
        v___x_3963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3963_, 0, v___x_3962_);
        crate::leanh::lean_ctor_set(v___x_3963_, 1, v_a_3961_);
        v_sz_3964_ = lean_array_size(v_tail_3958_);
        v___x_3965_ = 0usize;
        v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3953_, v_tail_3958_, v_sz_3964_, v___x_3965_, v___x_3963_);
        v_fst_3967_ = crate::leanh::lean_ctor_get(v___x_3966_, 0);
        crate::leanh::lean_inc(v_fst_3967_);
        if crate::leanh::lean_obj_tag(v_fst_3967_) == 0 {
            let mut v_snd_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_3968_ = crate::leanh::lean_ctor_get(v___x_3966_, 1);
            crate::leanh::lean_inc(v_snd_3968_);
            crate::leanh::lean_dec_ref(v___x_3966_);
            return v_snd_3968_;
        } else {
            let mut v_val_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3966_);
            v_val_3969_ = crate::leanh::lean_ctor_get(v_fst_3967_, 0);
            crate::leanh::lean_inc(v_val_3969_);
            crate::leanh::lean_dec_ref_known(v_fst_3967_, 1);
            return v_val_3969_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(
    mut v_text_3970_: *mut crate::leanh::LeanObject,
    mut v_t_3971_: *mut crate::leanh::LeanObject,
    mut v_init_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_3970_, v_t_3971_, v_init_3972_);
    crate::leanh::lean_dec_ref(v_t_3971_);
    crate::leanh::lean_dec_ref(v_text_3970_);
    return v_res_3974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(
    mut v_sz_3975_: usize,
    mut v_i_3976_: usize,
    mut v_bs_3977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3978_: u8 = 0;
    let mut v_v_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3978_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
                if v___x_3978_ == 0 {
                    return v_bs_3977_;
                } else {
                    v_v_3979_ = lean_array_uget_borrowed(v_bs_3977_, v_i_3976_);
                    v_diagnostics_3980_ = crate::leanh::lean_ctor_get(v_v_3979_, 1);
                    v_msgLog_3981_ = crate::leanh::lean_ctor_get(v_diagnostics_3980_, 0);
                    crate::leanh::lean_inc_ref(v_msgLog_3981_);
                    v___x_3982_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3983_ = lean_array_uset(v_bs_3977_, v_i_3976_, v___x_3982_);
                    v___x_3984_ = 1usize;
                    v___x_3985_ = lean_usize_add(v_i_3976_, v___x_3984_);
                    v___x_3986_ = lean_array_uset(v_bs_x27_3983_, v_i_3976_, v_msgLog_3981_);
                    v_i_3976_ = v___x_3985_;
                    v_bs_3977_ = v___x_3986_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2___boxed(
    mut v_sz_3988_: *mut crate::leanh::LeanObject,
    mut v_i_3989_: *mut crate::leanh::LeanObject,
    mut v_bs_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3991_: usize = 0;
    let mut v_i_boxed_3992_: usize = 0;
    let mut v_res_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3991_ = crate::leanh::lean_unbox_usize(v_sz_3988_);
    crate::leanh::lean_dec(v_sz_3988_);
    v_i_boxed_3992_ = crate::leanh::lean_unbox_usize(v_i_3989_);
    crate::leanh::lean_dec(v_i_3989_);
    v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_boxed_3991_, v_i_boxed_3992_, v_bs_3990_);
    return v_res_3993_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3995_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3996_ = lean_mk_empty_array_with_capacity(v___x_3995_);
    v___x_3997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3997_, 0, v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3998_: usize = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = 5usize;
    v___x_3999_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4000_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4001_ = lean_mk_empty_array_with_capacity(v___x_4000_);
    v___x_4002_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1,
    );
    v___x_4003_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4003_, 0, v___x_4002_);
    crate::leanh::lean_ctor_set(v___x_4003_, 1, v___x_4001_);
    crate::leanh::lean_ctor_set(v___x_4003_, 2, v___x_3999_);
    crate::leanh::lean_ctor_set(v___x_4003_, 3, v___x_3999_);
    crate::leanh::lean_ctor_set_usize(v___x_4003_, 4, v___x_3998_);
    return v___x_4003_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4004_ = l_Lean_NameSet_empty;
    v___x_4005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2,
    );
    v___x_4006_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4006_, 0, v___x_4005_);
    crate::leanh::lean_ctor_set(v___x_4006_, 1, v___x_4005_);
    crate::leanh::lean_ctor_set(v___x_4006_, 2, v___x_4004_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(
    mut v_doc_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_meta_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSnap_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snaps_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4050_: usize = 0;
    let mut v___x_4051_: usize = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: usize = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v_processedSnap_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_unused_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4011_ = crate::leanh::lean_ctor_get(v_doc_4009_, 0);
                v_isSharedCheck_4076_ = (!crate::leanh::lean_is_exclusive(v_doc_4009_)) as u8;
                if v_isSharedCheck_4076_ == 0 {
                    v_unused_4077_ = crate::leanh::lean_ctor_get(v_doc_4009_, 1);
                    crate::leanh::lean_dec(v_unused_4077_);
                    v___x_4013_ = v_doc_4009_;
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toEditableDocumentCore_4011_);
                    crate::leanh::lean_dec(v_doc_4009_);
                    v___x_4013_ = crate::leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4015_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 0);
                crate::leanh::lean_inc_ref(v_meta_4015_);
                v_initSnap_4016_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 1);
                crate::leanh::lean_inc_ref(v_initSnap_4016_);
                v_cmdSnaps_4017_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 2);
                crate::leanh::lean_inc(v_cmdSnaps_4017_);
                crate::leanh::lean_dec_ref(v_toEditableDocumentCore_4011_);
                v_text_4018_ = crate::leanh::lean_ctor_get(v_meta_4015_, 3);
                crate::leanh::lean_inc_ref(v_text_4018_);
                crate::leanh::lean_dec_ref(v_meta_4015_);
                v_toSnapshot_4030_ = crate::leanh::lean_ctor_get(v_initSnap_4016_, 0);
                crate::leanh::lean_inc_ref(v_toSnapshot_4030_);
                v_metaSnap_4031_ = crate::leanh::lean_ctor_get(v_initSnap_4016_, 1);
                crate::leanh::lean_inc_ref(v_metaSnap_4031_);
                v_result_x3f_4032_ = crate::leanh::lean_ctor_get(v_initSnap_4016_, 4);
                crate::leanh::lean_inc(v_result_x3f_4032_);
                crate::leanh::lean_dec_ref(v_initSnap_4016_);
                v___f_4033_ =
                    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0;
                if crate::leanh::lean_obj_tag(v_result_x3f_4032_) == 0 {
                    v___x_4061_ = crate::leanh::lean_box(0);
                    v___y_4035_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_val_4062_ = crate::leanh::lean_ctor_get(v_result_x3f_4032_, 0);
                    v_isSharedCheck_4075_ =
                        (!crate::leanh::lean_is_exclusive(v_result_x3f_4032_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4064_ = v_result_x3f_4032_;
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4062_);
                        crate::leanh::lean_dec(v_result_x3f_4032_);
                        v___x_4064_ = crate::leanh::lean_box(0);
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_ranges_4021_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                v___x_4022_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_4018_, v_unreported_4020_, v_ranges_4021_);
                crate::leanh::lean_dec_ref(v_unreported_4020_);
                crate::leanh::lean_dec_ref(v_text_4018_);
                v___x_4023_ = l_IO_AsyncList_waitAll___redArg(v_cmdSnaps_4017_);
                v___x_4024_ = lean_task_get_own(v___x_4023_);
                v_fst_4025_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                crate::leanh::lean_inc(v_fst_4025_);
                crate::leanh::lean_dec(v___x_4024_);
                v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_fst_4025_, v_fst_4025_, v___x_4022_);
                crate::leanh::lean_dec(v_fst_4025_);
                return v___x_4026_;
            }
            3 => {
                v_unreported_4029_ = crate::leanh::lean_ctor_get(v___y_4028_, 1);
                crate::leanh::lean_inc_ref(v_unreported_4029_);
                crate::leanh::lean_dec_ref(v___y_4028_);
                v_unreported_4020_ = v_unreported_4029_;
                state = 2;
                continue;
            }
            4 => {
                v_stx_x3f_4036_ = crate::leanh::lean_ctor_get(v_metaSnap_4031_, 0);
                crate::leanh::lean_inc(v_stx_x3f_4036_);
                v_reportingRange_4037_ = crate::leanh::lean_ctor_get(v_metaSnap_4031_, 1);
                crate::leanh::lean_inc(v_reportingRange_4037_);
                v___x_4038_ = 1;
                v___x_4039_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_4031_,
                    v___f_4033_,
                    v_stx_x3f_4036_,
                    v_reportingRange_4037_,
                    v___x_4038_,
                );
                v___x_4040_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_4040_);
                v___x_4042_ = lean_array_push(v___x_4041_, v___x_4039_);
                v___x_4043_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_4035_, v___x_4042_);
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4043_);
                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v_toSnapshot_4030_);
                    v___x_4045_ = v___x_4013_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_toSnapshot_4030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4043_);
                    v___x_4045_ = v_reuseFailAlloc_4060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_snaps_4046_ = l_Lean_Language_SnapshotTree_getAll(v___x_4045_);
                v___x_4047_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
                v___x_4049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3);
                v_sz_4050_ = lean_array_size(v_snaps_4046_);
                v___x_4051_ = 0usize;
                v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_4050_, v___x_4051_, v_snaps_4046_);
                v___x_4053_ = lean_array_get_size(v___x_4052_);
                v___x_4054_ = lean_nat_dec_lt(v___x_4047_, v___x_4053_);
                if v___x_4054_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4052_);
                    v_unreported_4020_ = v___x_4048_;
                    state = 2;
                    continue;
                } else {
                    v___x_4055_ = lean_nat_dec_le(v___x_4053_, v___x_4053_);
                    if v___x_4055_ == 0 {
                        if v___x_4054_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4052_);
                            v_unreported_4020_ = v___x_4048_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4056_ = lean_usize_of_nat(v___x_4053_);
                            v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4056_, v___x_4049_);
                            crate::leanh::lean_dec_ref(v___x_4052_);
                            v___y_4028_ = v___x_4057_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4058_ = lean_usize_of_nat(v___x_4053_);
                        v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4058_, v___x_4049_);
                        crate::leanh::lean_dec_ref(v___x_4052_);
                        v___y_4028_ = v___x_4059_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                v_processedSnap_4066_ = crate::leanh::lean_ctor_get(v_val_4062_, 1);
                crate::leanh::lean_inc_ref(v_processedSnap_4066_);
                crate::leanh::lean_dec(v_val_4062_);
                v_stx_x3f_4067_ = crate::leanh::lean_ctor_get(v_processedSnap_4066_, 0);
                crate::leanh::lean_inc(v_stx_x3f_4067_);
                v_reportingRange_4068_ = crate::leanh::lean_ctor_get(v_processedSnap_4066_, 1);
                crate::leanh::lean_inc(v_reportingRange_4068_);
                v___f_4069_ =
                    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4;
                v___x_4070_ = 1;
                v___x_4071_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_processedSnap_4066_,
                    v___f_4069_,
                    v_stx_x3f_4067_,
                    v_reportingRange_4068_,
                    v___x_4070_,
                );
                if v_isShared_4065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4071_);
                    v___x_4073_ = v___x_4064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4074_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4035_ = v___x_4073_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___boxed(
    mut v_doc_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(v_doc_4078_);
    return v_res_4080_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(
    mut v_as_4081_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4082_: *mut crate::leanh::LeanObject,
    mut v_b_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_4081_, v_as_x27_4082_, v_b_4083_);
    return v___x_4086_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(
    mut v_as_4087_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4088_: *mut crate::leanh::LeanObject,
    mut v_b_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(v_as_4087_, v_as_x27_4088_, v_b_4089_, v_a_4090_);
    crate::leanh::lean_dec(v_as_x27_4088_);
    crate::leanh::lean_dec(v_as_4087_);
    return v_res_4092_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(
    mut v_as_4093_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4094_: *mut crate::leanh::LeanObject,
    mut v_b_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_4094_, v_b_4095_);
    return v___x_4098_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(
    mut v_as_4099_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4100_: *mut crate::leanh::LeanObject,
    mut v_b_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4104_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(v_as_4099_, v_as_x27_4100_, v_b_4101_, v_a_4102_);
    crate::leanh::lean_dec(v_as_x27_4100_);
    crate::leanh::lean_dec(v_as_4099_);
    return v_res_4104_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___y_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4123_: u8 = 0;
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_id_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4105_) == 0 {
                    v___x_4107_ = l_List_reverse___redArg(v_a_4106_);
                    return v___x_4107_;
                } else {
                    v_head_4108_ = crate::leanh::lean_ctor_get(v_a_4105_, 0);
                    v_tail_4109_ = crate::leanh::lean_ctor_get(v_a_4105_, 1);
                    v_isSharedCheck_4138_ = (!crate::leanh::lean_is_exclusive(v_a_4105_)) as u8;
                    if v_isSharedCheck_4138_ == 0 {
                        v___x_4111_ = v_a_4105_;
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4109_);
                        crate::leanh::lean_inc(v_head_4108_);
                        crate::leanh::lean_dec(v_a_4105_);
                        v___x_4111_ = crate::leanh::lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_head_4108_) == 0 {
                    v_ns_4119_ = crate::leanh::lean_ctor_get(v_head_4108_, 0);
                    v_except_4120_ = crate::leanh::lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4122_ = v_head_4108_;
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_except_4120_);
                        crate::leanh::lean_inc(v_ns_4119_);
                        crate::leanh::lean_dec(v_head_4108_);
                        v___x_4122_ = crate::leanh::lean_box(0);
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_id_4129_ = crate::leanh::lean_ctor_get(v_head_4108_, 0);
                    v_declName_4130_ = crate::leanh::lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4137_ = (!crate::leanh::lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4132_ = v_head_4108_;
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_4130_);
                        crate::leanh::lean_inc(v_id_4129_);
                        crate::leanh::lean_dec(v_head_4108_);
                        v___x_4132_ = crate::leanh::lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4111_, 1, v_a_4106_);
                    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___y_4114_);
                    v___x_4116_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___y_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_a_4106_);
                    v___x_4116_ = v_reuseFailAlloc_4118_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_4105_ = v_tail_4109_;
                v_a_4106_ = v___x_4116_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4124_ = lean_array_mk(v_except_4120_);
                if v_isShared_4123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4122_, 1, v___x_4124_);
                    v___x_4126_ = v___x_4122_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_ns_4119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4124_);
                    v___x_4126_ = v_reuseFailAlloc_4127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4114_ = v___x_4126_;
                state = 2;
                continue;
            }
            6 => {
                if v_isShared_4133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4132_, 1, v_id_4129_);
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v_declName_4130_);
                    v___x_4135_ = v___x_4132_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_declName_4130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_id_4129_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4114_ = v___x_4135_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(
    mut v_a_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4142_ = crate::leanh::lean_ctor_get(v_a_4141_, 0);
                v_snd_4143_ = crate::leanh::lean_ctor_get(v_a_4141_, 1);
                v_isSharedCheck_4159_ = (!crate::leanh::lean_is_exclusive(v_a_4141_)) as u8;
                if v_isSharedCheck_4159_ == 0 {
                    v___x_4145_ = v_a_4141_;
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4143_);
                    crate::leanh::lean_inc(v_fst_4142_);
                    crate::leanh::lean_dec(v_a_4141_);
                    v___x_4145_ = crate::leanh::lean_box(0);
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4147_ = l_Lean_Name_isAnonymous(v_snd_4143_);
                if v___x_4147_ == 0 {
                    v___x_4148_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    crate::leanh::lean_inc(v_snd_4143_);
                    v___x_4149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4149_, 0, v_snd_4143_);
                    crate::leanh::lean_ctor_set(v___x_4149_, 1, v___x_4148_);
                    v___x_4150_ = lean_array_push(v_fst_4142_, v___x_4149_);
                    v___x_4151_ = l_Lean_Name_getPrefix(v_snd_4143_);
                    crate::leanh::lean_dec(v_snd_4143_);
                    if v_isShared_4146_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4145_, 1, v___x_4151_);
                        crate::leanh::lean_ctor_set(v___x_4145_, 0, v___x_4150_);
                        v___x_4153_ = v___x_4145_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4150_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4151_);
                        v___x_4153_ = v_reuseFailAlloc_4155_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4146_ == 0 {
                        v___x_4157_ = v___x_4145_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_fst_4142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_snd_4143_);
                        v___x_4157_ = v_reuseFailAlloc_4158_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_a_4141_ = v___x_4153_;
                state = 0;
                continue;
            }
            3 => {
                return v___x_4157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_collectOpenNamespaces(
    mut v_currentNamespace_4162_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_openNamespaces_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_openNamespaces_4164_ = l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0;
    v___x_4165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4165_, 0, v_openNamespaces_4164_);
    crate::leanh::lean_ctor_set(v___x_4165_, 1, v_currentNamespace_4162_);
    v___x_4166_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v___x_4165_);
    v_fst_4167_ = crate::leanh::lean_ctor_get(v___x_4166_, 0);
    crate::leanh::lean_inc(v_fst_4167_);
    crate::leanh::lean_dec_ref(v___x_4166_);
    v___x_4168_ = crate::leanh::lean_box(0);
    v___x_4169_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
        v_openDecls_4163_,
        v___x_4168_,
    );
    v___x_4170_ = lean_array_mk(v___x_4169_);
    v___x_4171_ = l_Array_append___redArg(v_fst_4167_, v___x_4170_);
    crate::leanh::lean_dec_ref(v___x_4170_);
    return v___x_4171_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(
    mut v_inst_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v_a_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
    mut v_doc_4175_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4176_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4177_: *mut crate::leanh::LeanObject,
    mut v_val_4178_: *mut crate::leanh::LeanObject,
    mut v_val_4179_: *mut crate::leanh::LeanObject,
    mut v___x_4180_: u8,
    mut v_decl_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v_meta_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v_text_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minimizedId_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_unused_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4206_: u8 = 0;
    let mut v_unused_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4182_ = crate::leanh::lean_ctor_get(v_doc_4175_, 0);
                v_isSharedCheck_4206_ = (!crate::leanh::lean_is_exclusive(v_doc_4175_)) as u8;
                if v_isSharedCheck_4206_ == 0 {
                    v_unused_4207_ = crate::leanh::lean_ctor_get(v_doc_4175_, 1);
                    crate::leanh::lean_dec(v_unused_4207_);
                    v___x_4184_ = v_doc_4175_;
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toEditableDocumentCore_4182_);
                    crate::leanh::lean_dec(v_doc_4175_);
                    v___x_4184_ = crate::leanh::lean_box(0);
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4186_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 0);
                v_isSharedCheck_4202_ =
                    (!crate::leanh::lean_is_exclusive(v_toEditableDocumentCore_4182_)) as u8;
                if v_isSharedCheck_4202_ == 0 {
                    v_unused_4203_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 3);
                    crate::leanh::lean_dec(v_unused_4203_);
                    v_unused_4204_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 2);
                    crate::leanh::lean_dec(v_unused_4204_);
                    v_unused_4205_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 1);
                    crate::leanh::lean_dec(v_unused_4205_);
                    v___x_4188_ = v_toEditableDocumentCore_4182_;
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_meta_4186_);
                    crate::leanh::lean_dec(v_toEditableDocumentCore_4182_);
                    v___x_4188_ = crate::leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4190_ = crate::leanh::lean_ctor_get(v_meta_4186_, 3);
                crate::leanh::lean_inc_ref(v_text_4190_);
                crate::leanh::lean_dec_ref(v_meta_4186_);
                v_minimizedId_4191_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(
                    v_currNamespace_4176_,
                    v_openDecls_4177_,
                    v_decl_4181_,
                );
                if v_isShared_4185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4184_, 1, v_val_4179_);
                    crate::leanh::lean_ctor_set(v___x_4184_, 0, v_val_4178_);
                    v___x_4193_ = v___x_4184_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 1, v_val_4179_);
                    v___x_4193_ = v_reuseFailAlloc_4201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4194_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4190_, v___x_4193_);
                crate::leanh::lean_inc(v_minimizedId_4191_);
                v___x_4195_ = l_Lean_Name_toString(v_minimizedId_4191_, v___x_4180_);
                v___x_4196_ = crate::leanh::lean_box(0);
                if v_isShared_4189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4188_, 3, v___x_4196_);
                    crate::leanh::lean_ctor_set(v___x_4188_, 2, v___x_4196_);
                    crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4195_);
                    crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4194_);
                    v___x_4198_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 2, v___x_4196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 3, v___x_4196_);
                    v___x_4198_ = v_reuseFailAlloc_4200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4199_, 0, v_minimizedId_4191_);
                crate::leanh::lean_ctor_set(v___x_4199_, 1, v___x_4198_);
                return v___x_4199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(
    mut v_doc_4208_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4209_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4210_: *mut crate::leanh::LeanObject,
    mut v_val_4211_: *mut crate::leanh::LeanObject,
    mut v_val_4212_: *mut crate::leanh::LeanObject,
    mut v___x_4213_: *mut crate::leanh::LeanObject,
    mut v_decl_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_172__boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_172__boxed_4215_ = (crate::leanh::lean_unbox(v___x_4213_) as u8);
    v_res_4216_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
        v_doc_4208_,
        v_currNamespace_4209_,
        v_openDecls_4210_,
        v_val_4211_,
        v_val_4212_,
        v___x_172__boxed_4215_,
        v_decl_4214_,
    );
    crate::leanh::lean_dec(v_openDecls_4210_);
    return v_res_4216_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f(
    mut v_doc_4217_: *mut crate::leanh::LeanObject,
    mut v_ctx_4218_: *mut crate::leanh::LeanObject,
    mut v_stx_4219_: *mut crate::leanh::LeanObject,
    mut v_id_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v_currNamespace_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = 1;
                v___x_4222_ = l_Lean_Syntax_getPos_x3f(v_stx_4219_, v___x_4221_);
                if crate::leanh::lean_obj_tag(v___x_4222_) == 1 {
                    v_val_4223_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    crate::leanh::lean_inc(v_val_4223_);
                    crate::leanh::lean_dec_ref_known(v___x_4222_, 1);
                    v___x_4224_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4219_, v___x_4221_);
                    if crate::leanh::lean_obj_tag(v___x_4224_) == 1 {
                        v_toCommandContextInfo_4225_ = crate::leanh::lean_ctor_get(v_ctx_4218_, 0);
                        v_val_4226_ = crate::leanh::lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4241_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4241_ == 0 {
                            v___x_4228_ = v___x_4224_;
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4226_);
                            crate::leanh::lean_dec(v___x_4224_);
                            v___x_4228_ = crate::leanh::lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4224_);
                        crate::leanh::lean_dec(v_val_4223_);
                        crate::leanh::lean_dec(v_id_4220_);
                        crate::leanh::lean_dec_ref(v_ctx_4218_);
                        crate::leanh::lean_dec_ref(v_doc_4217_);
                        v___x_4242_ = crate::leanh::lean_box(0);
                        return v___x_4242_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4222_);
                    crate::leanh::lean_dec(v_id_4220_);
                    crate::leanh::lean_dec_ref(v_ctx_4218_);
                    crate::leanh::lean_dec_ref(v_doc_4217_);
                    v___x_4243_ = crate::leanh::lean_box(0);
                    return v___x_4243_;
                }
            }
            1 => {
                v_currNamespace_4230_ =
                    crate::leanh::lean_ctor_get(v_toCommandContextInfo_4225_, 5);
                v_openDecls_4231_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_4225_, 6);
                v___x_4232_ = l_Lean_Name_toString(v_id_4220_, v___x_4221_);
                v___x_4233_ = crate::leanh::lean_box((v___x_4221_) as usize);
                crate::leanh::lean_inc_n(v_openDecls_4231_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_4230_, 2);
                v___f_4234_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_4234_, 0, v_doc_4217_);
                crate::leanh::lean_closure_set(v___f_4234_, 1, v_currNamespace_4230_);
                crate::leanh::lean_closure_set(v___f_4234_, 2, v_openDecls_4231_);
                crate::leanh::lean_closure_set(v___f_4234_, 3, v_val_4223_);
                crate::leanh::lean_closure_set(v___f_4234_, 4, v_val_4226_);
                crate::leanh::lean_closure_set(v___f_4234_, 5, v___x_4233_);
                v___x_4235_ = l_Lean_Server_FileWorker_collectOpenNamespaces(
                    v_currNamespace_4230_,
                    v_openDecls_4231_,
                );
                v___x_4236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4236_, 0, v___x_4232_);
                crate::leanh::lean_ctor_set(v___x_4236_, 1, v___x_4235_);
                v___x_4237_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                crate::leanh::lean_ctor_set(v___x_4237_, 1, v_ctx_4218_);
                crate::leanh::lean_ctor_set(v___x_4237_, 2, v___f_4234_);
                if v_isShared_4229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4228_, 0, v___x_4237_);
                    v___x_4239_ = v___x_4228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
                    v___x_4239_ = v_reuseFailAlloc_4240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(
    mut v_doc_4244_: *mut crate::leanh::LeanObject,
    mut v_ctx_4245_: *mut crate::leanh::LeanObject,
    mut v_stx_4246_: *mut crate::leanh::LeanObject,
    mut v_id_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(
        v_doc_4244_,
        v_ctx_4245_,
        v_stx_4246_,
        v_id_4247_,
    );
    crate::leanh::lean_dec(v_stx_4246_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(
    mut v_e_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4252_ = l_Lean_Expr_hasMVar(v_e_4249_);
                if v___x_4252_ == 0 {
                    v___x_4253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4253_, 0, v_e_4249_);
                    return v___x_4253_;
                } else {
                    v___x_4254_ = lean_st_ref_get(v___y_4250_);
                    v_mctx_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4255_);
                    crate::leanh::lean_dec(v___x_4254_);
                    v___x_4256_ = l_Lean_instantiateMVarsCore(v_mctx_4255_, v_e_4249_);
                    v_fst_4257_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                    crate::leanh::lean_inc(v_fst_4257_);
                    v_snd_4258_ = crate::leanh::lean_ctor_get(v___x_4256_, 1);
                    crate::leanh::lean_inc(v_snd_4258_);
                    crate::leanh::lean_dec_ref(v___x_4256_);
                    v___x_4259_ = lean_st_ref_take(v___y_4250_);
                    v_cache_4260_ = crate::leanh::lean_ctor_get(v___x_4259_, 1);
                    v_zetaDeltaFVarIds_4261_ = crate::leanh::lean_ctor_get(v___x_4259_, 2);
                    v_postponed_4262_ = crate::leanh::lean_ctor_get(v___x_4259_, 3);
                    v_diag_4263_ = crate::leanh::lean_ctor_get(v___x_4259_, 4);
                    v_isSharedCheck_4272_ = (!crate::leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4272_ == 0 {
                        v_unused_4273_ = crate::leanh::lean_ctor_get(v___x_4259_, 0);
                        crate::leanh::lean_dec(v_unused_4273_);
                        v___x_4265_ = v___x_4259_;
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4263_);
                        crate::leanh::lean_inc(v_postponed_4262_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4261_);
                        crate::leanh::lean_inc(v_cache_4260_);
                        crate::leanh::lean_dec(v___x_4259_);
                        v___x_4265_ = crate::leanh::lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4266_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4265_, 0, v_snd_4258_);
                    v___x_4268_ = v___x_4265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_snd_4258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_cache_4260_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4271_,
                        2,
                        v_zetaDeltaFVarIds_4261_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_postponed_4262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_diag_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4269_ = lean_st_ref_set(v___y_4250_, v___x_4268_);
                v___x_4270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4270_, 0, v_fst_4257_);
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(
    mut v_e_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4274_, v___y_4275_);
    crate::leanh::lean_dec(v___y_4275_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
    mut v_e_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4278_, v___y_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(
    mut v_e_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ =
        l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
            v_e_4285_,
            v___y_4286_,
            v___y_4287_,
            v___y_4288_,
            v___y_4289_,
        );
    crate::leanh::lean_dec(v___y_4289_);
    crate::leanh::lean_dec_ref(v___y_4288_);
    crate::leanh::lean_dec(v___y_4287_);
    crate::leanh::lean_dec_ref(v___y_4286_);
    return v_res_4291_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(
    mut v_expr_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v_a_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4296_);
                crate::leanh::lean_inc_ref(v___y_4295_);
                crate::leanh::lean_inc(v___y_4294_);
                crate::leanh::lean_inc_ref(v___y_4293_);
                v___x_4308_ = lean_infer_type(
                    v_expr_4292_,
                    v___y_4293_,
                    v___y_4294_,
                    v___y_4295_,
                    v___y_4296_,
                );
                if crate::leanh::lean_obj_tag(v___x_4308_) == 0 {
                    v_a_4309_ = crate::leanh::lean_ctor_get(v___x_4308_, 0);
                    crate::leanh::lean_inc(v_a_4309_);
                    crate::leanh::lean_dec_ref_known(v___x_4308_, 1);
                    v___x_4310_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_4309_, v___y_4294_);
                    v_a_4311_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4328_ = (!crate::leanh::lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4313_ = v___x_4310_;
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4311_);
                        crate::leanh::lean_dec(v___x_4310_);
                        v___x_4313_ = crate::leanh::lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4296_);
                    crate::leanh::lean_dec_ref(v___y_4295_);
                    crate::leanh::lean_dec(v___y_4294_);
                    crate::leanh::lean_dec_ref(v___y_4293_);
                    v_a_4329_ = crate::leanh::lean_ctor_get(v___x_4308_, 0);
                    crate::leanh::lean_inc(v_a_4329_);
                    crate::leanh::lean_dec_ref_known(v___x_4308_, 1);
                    v_a_4305_ = v_a_4329_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_4300_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4299_);
                    v___x_4301_ = crate::leanh::lean_box(0);
                    v___x_4302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
                    return v___x_4302_;
                } else {
                    v___x_4303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4303_, 0, v___y_4299_);
                    return v___x_4303_;
                }
            }
            2 => {
                v___x_4306_ = l_Lean_Exception_isInterrupt(v_a_4305_);
                if v___x_4306_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_4305_);
                    v___x_4307_ = l_Lean_Exception_isRuntime(v_a_4305_);
                    v___y_4299_ = v_a_4305_;
                    v___y_4300_ = v___x_4307_;
                    state = 1;
                    continue;
                } else {
                    v___y_4299_ = v_a_4305_;
                    v___y_4300_ = v___x_4306_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4315_ = l_Lean_Server_Completion_getDotCompletionTypeNames(
                    v_a_4311_,
                    v___y_4293_,
                    v___y_4294_,
                    v___y_4295_,
                    v___y_4296_,
                );
                crate::leanh::lean_dec(v___y_4296_);
                crate::leanh::lean_dec_ref(v___y_4295_);
                crate::leanh::lean_dec(v___y_4294_);
                crate::leanh::lean_dec_ref(v___y_4293_);
                if crate::leanh::lean_obj_tag(v___x_4315_) == 0 {
                    v_a_4316_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4326_ = (!crate::leanh::lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4318_ = v___x_4315_;
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4316_);
                        crate::leanh::lean_dec(v___x_4315_);
                        v___x_4318_ = crate::leanh::lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4313_);
                    v_a_4327_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                    crate::leanh::lean_inc(v_a_4327_);
                    crate::leanh::lean_dec_ref_known(v___x_4315_, 1);
                    v_a_4305_ = v_a_4327_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_4314_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4313_, 1);
                    crate::leanh::lean_ctor_set(v___x_4313_, 0, v_a_4316_);
                    v___x_4321_ = v___x_4313_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4321_);
                    v___x_4323_ = v___x_4318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
                    v___x_4323_ = v_reuseFailAlloc_4324_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed(
    mut v_expr_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4336_ = l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(
        v_expr_4330_,
        v___y_4331_,
        v___y_4332_,
        v___y_4333_,
        v___y_4334_,
    );
    return v_res_4336_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(
    mut v_val_4337_: *mut crate::leanh::LeanObject,
    mut v_val_4338_: *mut crate::leanh::LeanObject,
    mut v_text_4339_: *mut crate::leanh::LeanObject,
    mut v_decl_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4341_, 0, v_val_4337_);
    crate::leanh::lean_ctor_set(v___x_4341_, 1, v_val_4338_);
    v___x_4342_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4339_, v___x_4341_);
    v___x_4343_ = l_Lean_Name_getString_x21(v_decl_4340_);
    v___x_4344_ = crate::leanh::lean_box(0);
    v___x_4345_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4342_);
    crate::leanh::lean_ctor_set(v___x_4345_, 1, v___x_4343_);
    crate::leanh::lean_ctor_set(v___x_4345_, 2, v___x_4344_);
    crate::leanh::lean_ctor_set(v___x_4345_, 3, v___x_4344_);
    v___x_4346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4346_, 0, v_decl_4340_);
    crate::leanh::lean_ctor_set(v___x_4346_, 1, v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(
    mut v_sz_4347_: usize,
    mut v_i_4348_: usize,
    mut v_bs_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: u8 = 0;
    let mut v_v_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: usize = 0;
    let mut v___x_4357_: usize = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4350_ = lean_usize_dec_lt(v_i_4348_, v_sz_4347_);
                if v___x_4350_ == 0 {
                    return v_bs_4349_;
                } else {
                    v_v_4351_ = lean_array_uget(v_bs_4349_, v_i_4348_);
                    v___x_4352_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4353_ = lean_array_uset(v_bs_4349_, v_i_4348_, v___x_4352_);
                    v___x_4354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    v___x_4355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4355_, 0, v_v_4351_);
                    crate::leanh::lean_ctor_set(v___x_4355_, 1, v___x_4354_);
                    v___x_4356_ = 1usize;
                    v___x_4357_ = lean_usize_add(v_i_4348_, v___x_4356_);
                    v___x_4358_ = lean_array_uset(v_bs_x27_4353_, v_i_4348_, v___x_4355_);
                    v_i_4348_ = v___x_4357_;
                    v_bs_4349_ = v___x_4358_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1___boxed(
    mut v_sz_4360_: *mut crate::leanh::LeanObject,
    mut v_i_4361_: *mut crate::leanh::LeanObject,
    mut v_bs_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4363_: usize = 0;
    let mut v_i_boxed_4364_: usize = 0;
    let mut v_res_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4363_ = crate::leanh::lean_unbox_usize(v_sz_4360_);
    crate::leanh::lean_dec(v_sz_4360_);
    v_i_boxed_4364_ = crate::leanh::lean_unbox_usize(v_i_4361_);
    crate::leanh::lean_dec(v_i_4361_);
    v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_4363_, v_i_boxed_4364_, v_bs_4362_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f(
    mut v_doc_4366_: *mut crate::leanh::LeanObject,
    mut v_ctx_4367_: *mut crate::leanh::LeanObject,
    mut v_ti_4368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toElabInfo_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v_val_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v_toEditableDocumentCore_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_meta_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4404_: usize = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_unused_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toElabInfo_4370_ = crate::leanh::lean_ctor_get(v_ti_4368_, 0);
                crate::leanh::lean_inc_ref(v_toElabInfo_4370_);
                v_lctx_4371_ = crate::leanh::lean_ctor_get(v_ti_4368_, 1);
                crate::leanh::lean_inc_ref(v_lctx_4371_);
                v_expr_4372_ = crate::leanh::lean_ctor_get(v_ti_4368_, 3);
                crate::leanh::lean_inc_ref(v_expr_4372_);
                crate::leanh::lean_dec_ref(v_ti_4368_);
                v_stx_4373_ = crate::leanh::lean_ctor_get(v_toElabInfo_4370_, 1);
                crate::leanh::lean_inc(v_stx_4373_);
                crate::leanh::lean_dec_ref(v_toElabInfo_4370_);
                v___x_4374_ = 1;
                v___x_4375_ = l_Lean_Syntax_getPos_x3f(v_stx_4373_, v___x_4374_);
                if crate::leanh::lean_obj_tag(v___x_4375_) == 1 {
                    v_val_4376_ = crate::leanh::lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4441_ = (!crate::leanh::lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4441_ == 0 {
                        v___x_4378_ = v___x_4375_;
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4376_);
                        crate::leanh::lean_dec(v___x_4375_);
                        v___x_4378_ = crate::leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4375_);
                    crate::leanh::lean_dec(v_stx_4373_);
                    crate::leanh::lean_dec_ref(v_expr_4372_);
                    crate::leanh::lean_dec_ref(v_lctx_4371_);
                    crate::leanh::lean_dec_ref(v_ctx_4367_);
                    crate::leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4442_ = crate::leanh::lean_box(0);
                    v___x_4443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4443_, 0, v___x_4442_);
                    return v___x_4443_;
                }
            }
            1 => {
                v___x_4380_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4373_, v___x_4374_);
                crate::leanh::lean_dec(v_stx_4373_);
                if crate::leanh::lean_obj_tag(v___x_4380_) == 1 {
                    crate::leanh::lean_del_object(v___x_4378_);
                    v_val_4381_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                    crate::leanh::lean_inc(v_val_4381_);
                    crate::leanh::lean_dec_ref_known(v___x_4380_, 1);
                    v___f_4382_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4382_, 0, v_expr_4372_);
                    crate::leanh::lean_inc_ref(v_ctx_4367_);
                    v___x_4383_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_4367_,
                        v_lctx_4371_,
                        v___f_4382_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4383_) == 0 {
                        v_a_4384_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4428_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4386_ = v___x_4383_;
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4384_);
                            crate::leanh::lean_dec(v___x_4383_);
                            v___x_4386_ = crate::leanh::lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4381_);
                        crate::leanh::lean_dec(v_val_4376_);
                        crate::leanh::lean_dec_ref(v_ctx_4367_);
                        crate::leanh::lean_dec_ref(v_doc_4366_);
                        v_a_4429_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4436_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4436_ == 0 {
                            v___x_4431_ = v___x_4383_;
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4429_);
                            crate::leanh::lean_dec(v___x_4383_);
                            v___x_4431_ = crate::leanh::lean_box(0);
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4380_);
                    crate::leanh::lean_dec(v_val_4376_);
                    crate::leanh::lean_dec_ref(v_expr_4372_);
                    crate::leanh::lean_dec_ref(v_lctx_4371_);
                    crate::leanh::lean_dec_ref(v_ctx_4367_);
                    crate::leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4437_ = crate::leanh::lean_box(0);
                    if v_isShared_4379_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4378_, 0);
                        crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4437_);
                        v___x_4439_ = v___x_4378_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
                        v___x_4439_ = v_reuseFailAlloc_4440_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4384_) == 1 {
                    v_val_4388_ = crate::leanh::lean_ctor_get(v_a_4384_, 0);
                    v_isSharedCheck_4423_ = (!crate::leanh::lean_is_exclusive(v_a_4384_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4390_ = v_a_4384_;
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4388_);
                        crate::leanh::lean_dec(v_a_4384_);
                        v___x_4390_ = crate::leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4384_);
                    crate::leanh::lean_dec(v_val_4381_);
                    crate::leanh::lean_dec(v_val_4376_);
                    crate::leanh::lean_dec_ref(v_ctx_4367_);
                    crate::leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4424_ = crate::leanh::lean_box(0);
                    if v_isShared_4387_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4424_);
                        v___x_4426_ = v___x_4386_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
                        v___x_4426_ = v_reuseFailAlloc_4427_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4392_ = lean_array_get_size(v_val_4388_);
                v___x_4393_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4394_ = lean_nat_dec_eq(v___x_4392_, v___x_4393_);
                if v___x_4394_ == 0 {
                    v_toEditableDocumentCore_4395_ = crate::leanh::lean_ctor_get(v_doc_4366_, 0);
                    v_isSharedCheck_4417_ = (!crate::leanh::lean_is_exclusive(v_doc_4366_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v_unused_4418_ = crate::leanh::lean_ctor_get(v_doc_4366_, 1);
                        crate::leanh::lean_dec(v_unused_4418_);
                        v___x_4397_ = v_doc_4366_;
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toEditableDocumentCore_4395_);
                        crate::leanh::lean_dec(v_doc_4366_);
                        v___x_4397_ = crate::leanh::lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4390_);
                    crate::leanh::lean_dec(v_val_4388_);
                    crate::leanh::lean_dec(v_val_4381_);
                    crate::leanh::lean_dec(v_val_4376_);
                    crate::leanh::lean_dec_ref(v_ctx_4367_);
                    crate::leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4419_ = crate::leanh::lean_box(0);
                    if v_isShared_4387_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4419_);
                        v___x_4421_ = v___x_4386_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_meta_4399_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4395_, 0);
                crate::leanh::lean_inc_ref(v_meta_4399_);
                crate::leanh::lean_dec_ref(v_toEditableDocumentCore_4395_);
                v_text_4400_ = crate::leanh::lean_ctor_get(v_meta_4399_, 3);
                crate::leanh::lean_inc_ref(v_text_4400_);
                crate::leanh::lean_dec_ref(v_meta_4399_);
                v_source_4401_ = crate::leanh::lean_ctor_get(v_text_4400_, 0);
                crate::leanh::lean_inc_ref(v_source_4401_);
                crate::leanh::lean_inc(v_val_4381_);
                crate::leanh::lean_inc(v_val_4376_);
                v___f_4402_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4402_, 0, v_val_4376_);
                crate::leanh::lean_closure_set(v___f_4402_, 1, v_val_4381_);
                crate::leanh::lean_closure_set(v___f_4402_, 2, v_text_4400_);
                v___x_4403_ = lean_string_utf8_extract(v_source_4401_, v_val_4376_, v_val_4381_);
                crate::leanh::lean_dec(v_val_4381_);
                crate::leanh::lean_dec(v_val_4376_);
                crate::leanh::lean_dec_ref(v_source_4401_);
                v_sz_4404_ = lean_array_size(v_val_4388_);
                v___x_4405_ = 0usize;
                v___x_4406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4404_, v___x_4405_, v_val_4388_);
                if v_isShared_4398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4397_, 1, v___x_4406_);
                    crate::leanh::lean_ctor_set(v___x_4397_, 0, v___x_4403_);
                    v___x_4408_ = v___x_4397_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4406_);
                    v___x_4408_ = v_reuseFailAlloc_4416_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4409_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4408_);
                crate::leanh::lean_ctor_set(v___x_4409_, 1, v_ctx_4367_);
                crate::leanh::lean_ctor_set(v___x_4409_, 2, v___f_4402_);
                if v_isShared_4391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4390_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4390_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4415_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4411_);
                    v___x_4413_ = v___x_4386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
                    v___x_4413_ = v_reuseFailAlloc_4414_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4413_;
            }
            8 => {
                return v___x_4421_;
            }
            9 => {
                return v___x_4426_;
            }
            10 => {
                if v_isShared_4432_ == 0 {
                    v___x_4434_ = v___x_4431_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
                    v___x_4434_ = v_reuseFailAlloc_4435_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4434_;
            }
            12 => {
                return v___x_4439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___boxed(
    mut v_doc_4444_: *mut crate::leanh::LeanObject,
    mut v_ctx_4445_: *mut crate::leanh::LeanObject,
    mut v_ti_4446_: *mut crate::leanh::LeanObject,
    mut v_a_4447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4448_ =
        l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_4444_, v_ctx_4445_, v_ti_4446_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(
    mut v_doc_4449_: *mut crate::leanh::LeanObject,
    mut v_val_4450_: *mut crate::leanh::LeanObject,
    mut v_val_4451_: *mut crate::leanh::LeanObject,
    mut v_decl_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v_meta_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4460_: u8 = 0;
    let mut v_text_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_unused_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_unused_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4453_ = crate::leanh::lean_ctor_get(v_doc_4449_, 0);
                v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v_doc_4449_)) as u8;
                if v_isSharedCheck_4476_ == 0 {
                    v_unused_4477_ = crate::leanh::lean_ctor_get(v_doc_4449_, 1);
                    crate::leanh::lean_dec(v_unused_4477_);
                    v___x_4455_ = v_doc_4449_;
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toEditableDocumentCore_4453_);
                    crate::leanh::lean_dec(v_doc_4449_);
                    v___x_4455_ = crate::leanh::lean_box(0);
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4457_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 0);
                v_isSharedCheck_4472_ =
                    (!crate::leanh::lean_is_exclusive(v_toEditableDocumentCore_4453_)) as u8;
                if v_isSharedCheck_4472_ == 0 {
                    v_unused_4473_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 3);
                    crate::leanh::lean_dec(v_unused_4473_);
                    v_unused_4474_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 2);
                    crate::leanh::lean_dec(v_unused_4474_);
                    v_unused_4475_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 1);
                    crate::leanh::lean_dec(v_unused_4475_);
                    v___x_4459_ = v_toEditableDocumentCore_4453_;
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_meta_4457_);
                    crate::leanh::lean_dec(v_toEditableDocumentCore_4453_);
                    v___x_4459_ = crate::leanh::lean_box(0);
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4461_ = crate::leanh::lean_ctor_get(v_meta_4457_, 3);
                crate::leanh::lean_inc_ref(v_text_4461_);
                crate::leanh::lean_dec_ref(v_meta_4457_);
                if v_isShared_4456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4455_, 1, v_val_4451_);
                    crate::leanh::lean_ctor_set(v___x_4455_, 0, v_val_4450_);
                    v___x_4463_ = v___x_4455_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_val_4450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_val_4451_);
                    v___x_4463_ = v_reuseFailAlloc_4471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4464_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4461_, v___x_4463_);
                v___x_4465_ = l_Lean_Name_getString_x21(v_decl_4452_);
                v___x_4466_ = crate::leanh::lean_box(0);
                if v_isShared_4460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4459_, 3, v___x_4466_);
                    crate::leanh::lean_ctor_set(v___x_4459_, 2, v___x_4466_);
                    crate::leanh::lean_ctor_set(v___x_4459_, 1, v___x_4465_);
                    crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4464_);
                    v___x_4468_ = v___x_4459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 2, v___x_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 3, v___x_4466_);
                    v___x_4468_ = v_reuseFailAlloc_4470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4469_, 0, v_decl_4452_);
                crate::leanh::lean_ctor_set(v___x_4469_, 1, v___x_4468_);
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
    mut v_doc_4478_: *mut crate::leanh::LeanObject,
    mut v_ctx_4479_: *mut crate::leanh::LeanObject,
    mut v_stx_4480_: *mut crate::leanh::LeanObject,
    mut v_id_4481_: *mut crate::leanh::LeanObject,
    mut v_lctx_4482_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: u8 = 0;
    let mut v___f_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_unused_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ = 1;
                v___x_4486_ = l_Lean_Syntax_getPos_x3f(v_stx_4480_, v___x_4485_);
                if crate::leanh::lean_obj_tag(v___x_4486_) == 1 {
                    v_val_4487_ = crate::leanh::lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4546_ = (!crate::leanh::lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4546_ == 0 {
                        v___x_4489_ = v___x_4486_;
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4487_);
                        crate::leanh::lean_dec(v___x_4486_);
                        v___x_4489_ = crate::leanh::lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4486_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4483_);
                    crate::leanh::lean_dec_ref(v_lctx_4482_);
                    crate::leanh::lean_dec(v_id_4481_);
                    crate::leanh::lean_dec_ref(v_ctx_4479_);
                    crate::leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4547_ = crate::leanh::lean_box(0);
                    v___x_4548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4547_);
                    return v___x_4548_;
                }
            }
            1 => {
                v___x_4491_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4480_, v___x_4485_);
                if crate::leanh::lean_obj_tag(v___x_4491_) == 1 {
                    crate::leanh::lean_del_object(v___x_4489_);
                    if crate::leanh::lean_obj_tag(v_expectedType_x3f_4483_) == 1 {
                        v_val_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                        crate::leanh::lean_inc(v_val_4492_);
                        crate::leanh::lean_dec_ref_known(v___x_4491_, 1);
                        v_val_4493_ = crate::leanh::lean_ctor_get(v_expectedType_x3f_4483_, 0);
                        v_isSharedCheck_4532_ =
                            (!crate::leanh::lean_is_exclusive(v_expectedType_x3f_4483_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4495_ = v_expectedType_x3f_4483_;
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4493_);
                            crate::leanh::lean_dec(v_expectedType_x3f_4483_);
                            v___x_4495_ = crate::leanh::lean_box(0);
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4487_);
                        crate::leanh::lean_dec(v_expectedType_x3f_4483_);
                        crate::leanh::lean_dec_ref(v_lctx_4482_);
                        crate::leanh::lean_dec(v_id_4481_);
                        crate::leanh::lean_dec_ref(v_ctx_4479_);
                        crate::leanh::lean_dec_ref(v_doc_4478_);
                        v_isSharedCheck_4540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4491_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v_unused_4541_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                            crate::leanh::lean_dec(v_unused_4541_);
                            v___x_4534_ = v___x_4491_;
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4491_);
                            v___x_4534_ = crate::leanh::lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4491_);
                    crate::leanh::lean_dec(v_val_4487_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4483_);
                    crate::leanh::lean_dec_ref(v_lctx_4482_);
                    crate::leanh::lean_dec(v_id_4481_);
                    crate::leanh::lean_dec_ref(v_ctx_4479_);
                    crate::leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4542_ = crate::leanh::lean_box(0);
                    if v_isShared_4490_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4489_, 0);
                        crate::leanh::lean_ctor_set(v___x_4489_, 0, v___x_4542_);
                        v___x_4544_ = v___x_4489_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4545_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
                        v___x_4544_ = v_reuseFailAlloc_4545_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4497_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed
                        as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4497_, 0, v_val_4493_);
                crate::leanh::lean_inc_ref(v_ctx_4479_);
                v___x_4498_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                    v_ctx_4479_,
                    v_lctx_4482_,
                    v___x_4497_,
                );
                if crate::leanh::lean_obj_tag(v___x_4498_) == 0 {
                    v_a_4499_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4523_ = (!crate::leanh::lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4523_ == 0 {
                        v___x_4501_ = v___x_4498_;
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4499_);
                        crate::leanh::lean_dec(v___x_4498_);
                        v___x_4501_ = crate::leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4495_);
                    crate::leanh::lean_dec(v_val_4492_);
                    crate::leanh::lean_dec(v_val_4487_);
                    crate::leanh::lean_dec(v_id_4481_);
                    crate::leanh::lean_dec_ref(v_ctx_4479_);
                    crate::leanh::lean_dec_ref(v_doc_4478_);
                    v_a_4524_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4531_ = (!crate::leanh::lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4531_ == 0 {
                        v___x_4526_ = v___x_4498_;
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4524_);
                        crate::leanh::lean_dec(v___x_4498_);
                        v___x_4526_ = crate::leanh::lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4503_ = lean_array_get_size(v_a_4499_);
                v___x_4504_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4505_ = lean_nat_dec_eq(v___x_4503_, v___x_4504_);
                if v___x_4505_ == 0 {
                    v___f_4506_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_4506_, 0, v_doc_4478_);
                    crate::leanh::lean_closure_set(v___f_4506_, 1, v_val_4487_);
                    crate::leanh::lean_closure_set(v___f_4506_, 2, v_val_4492_);
                    v___x_4507_ = l_Lean_Name_toString(v_id_4481_, v___x_4485_);
                    v_sz_4508_ = lean_array_size(v_a_4499_);
                    v___x_4509_ = 0usize;
                    v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4508_, v___x_4509_, v_a_4499_);
                    v___x_4511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4511_, 0, v___x_4507_);
                    crate::leanh::lean_ctor_set(v___x_4511_, 1, v___x_4510_);
                    v___x_4512_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    crate::leanh::lean_ctor_set(v___x_4512_, 1, v_ctx_4479_);
                    crate::leanh::lean_ctor_set(v___x_4512_, 2, v___f_4506_);
                    if v_isShared_4496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4512_);
                        v___x_4514_ = v___x_4495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4512_);
                        v___x_4514_ = v_reuseFailAlloc_4518_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4499_);
                    crate::leanh::lean_del_object(v___x_4495_);
                    crate::leanh::lean_dec(v_val_4492_);
                    crate::leanh::lean_dec(v_val_4487_);
                    crate::leanh::lean_dec(v_id_4481_);
                    crate::leanh::lean_dec_ref(v_ctx_4479_);
                    crate::leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4519_ = crate::leanh::lean_box(0);
                    if v_isShared_4502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4501_, 0, v___x_4519_);
                        v___x_4521_ = v___x_4501_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
                        v___x_4521_ = v_reuseFailAlloc_4522_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4501_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4501_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
                    v___x_4516_ = v_reuseFailAlloc_4517_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4516_;
            }
            6 => {
                return v___x_4521_;
            }
            7 => {
                if v_isShared_4527_ == 0 {
                    v___x_4529_ = v___x_4526_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4529_;
            }
            9 => {
                v___x_4536_ = crate::leanh::lean_box(0);
                if v_isShared_4535_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4534_, 0);
                    crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4536_);
                    v___x_4538_ = v___x_4534_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
                    v___x_4538_ = v_reuseFailAlloc_4539_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4538_;
            }
            11 => {
                return v___x_4544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(
    mut v_doc_4549_: *mut crate::leanh::LeanObject,
    mut v_ctx_4550_: *mut crate::leanh::LeanObject,
    mut v_stx_4551_: *mut crate::leanh::LeanObject,
    mut v_id_4552_: *mut crate::leanh::LeanObject,
    mut v_lctx_4553_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4554_: *mut crate::leanh::LeanObject,
    mut v_a_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4556_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
        v_doc_4549_,
        v_ctx_4550_,
        v_stx_4551_,
        v_id_4552_,
        v_lctx_4553_,
        v_expectedType_x3f_4554_,
    );
    crate::leanh::lean_dec(v_stx_4551_);
    return v_res_4556_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(
    mut v_doc_4557_: *mut crate::leanh::LeanObject,
    mut v_as_4558_: *mut crate::leanh::LeanObject,
    mut v_sz_4559_: usize,
    mut v_i_4560_: usize,
    mut v_b_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: usize = 0;
    let mut v_query_x3f_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: u8 = 0;
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termInfo_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_ctx_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4572_ = lean_usize_dec_lt(v_i_4560_, v_sz_4559_);
                if v___x_4572_ == 0 {
                    crate::leanh::lean_dec_ref(v_doc_4557_);
                    v___x_4573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4573_, 0, v_b_4561_);
                    return v___x_4573_;
                } else {
                    v_a_4574_ = lean_array_uget_borrowed(v_as_4558_, v_i_4560_);
                    v_fst_4575_ = crate::leanh::lean_ctor_get(v_a_4574_, 0);
                    v_info_4576_ = crate::leanh::lean_ctor_get(v_fst_4575_, 2);
                    match crate::leanh::lean_obj_tag(v_info_4576_) {
                        1 => {
                            v_ctx_4577_ = crate::leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4578_ = crate::leanh::lean_ctor_get(v_info_4576_, 0);
                            v_id_4579_ = crate::leanh::lean_ctor_get(v_info_4576_, 1);
                            crate::leanh::lean_inc(v_id_4579_);
                            crate::leanh::lean_inc_ref(v_ctx_4577_);
                            crate::leanh::lean_inc_ref(v_doc_4557_);
                            v___x_4580_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4577_,
                                v_stx_4578_,
                                v_id_4579_,
                            );
                            v_query_x3f_4569_ = v___x_4580_;
                            state = 2;
                            continue;
                        }
                        0 => {
                            v_ctx_4581_ = crate::leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_termInfo_4582_ = crate::leanh::lean_ctor_get(v_info_4576_, 0);
                            crate::leanh::lean_inc_ref(v_termInfo_4582_);
                            crate::leanh::lean_inc_ref(v_ctx_4581_);
                            crate::leanh::lean_inc_ref(v_doc_4557_);
                            v___x_4583_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4581_,
                                v_termInfo_4582_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4583_) == 0 {
                                v_a_4584_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                                crate::leanh::lean_inc(v_a_4584_);
                                crate::leanh::lean_dec_ref_known(v___x_4583_, 1);
                                v_query_x3f_4569_ = v_a_4584_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_4561_);
                                crate::leanh::lean_dec_ref(v_doc_4557_);
                                v_a_4585_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                                v_isSharedCheck_4593_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4583_)) as u8;
                                if v_isSharedCheck_4593_ == 0 {
                                    v___x_4587_ = v___x_4583_;
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4585_);
                                    crate::leanh::lean_dec(v___x_4583_);
                                    v___x_4587_ = crate::leanh::lean_box(0);
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        2 => {
                            v_ctx_4594_ = crate::leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4595_ = crate::leanh::lean_ctor_get(v_info_4576_, 0);
                            v_id_4596_ = crate::leanh::lean_ctor_get(v_info_4576_, 1);
                            v_lctx_4597_ = crate::leanh::lean_ctor_get(v_info_4576_, 2);
                            v_expectedType_x3f_4598_ = crate::leanh::lean_ctor_get(v_info_4576_, 3);
                            crate::leanh::lean_inc(v_expectedType_x3f_4598_);
                            crate::leanh::lean_inc_ref(v_lctx_4597_);
                            crate::leanh::lean_inc(v_id_4596_);
                            crate::leanh::lean_inc_ref(v_ctx_4594_);
                            crate::leanh::lean_inc_ref(v_doc_4557_);
                            v___x_4599_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4594_,
                                v_stx_4595_,
                                v_id_4596_,
                                v_lctx_4597_,
                                v_expectedType_x3f_4598_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4599_) == 0 {
                                v_a_4600_ = crate::leanh::lean_ctor_get(v___x_4599_, 0);
                                crate::leanh::lean_inc(v_a_4600_);
                                crate::leanh::lean_dec_ref_known(v___x_4599_, 1);
                                v_query_x3f_4569_ = v_a_4600_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_4561_);
                                crate::leanh::lean_dec_ref(v_doc_4557_);
                                v_a_4601_ = crate::leanh::lean_ctor_get(v___x_4599_, 0);
                                v_isSharedCheck_4609_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4599_)) as u8;
                                if v_isSharedCheck_4609_ == 0 {
                                    v___x_4603_ = v___x_4599_;
                                    v_isShared_4604_ = v_isSharedCheck_4609_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4601_);
                                    crate::leanh::lean_dec(v___x_4599_);
                                    v___x_4603_ = crate::leanh::lean_box(0);
                                    v_isShared_4604_ = v_isSharedCheck_4609_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_a_4564_ = v_b_4561_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4565_ = 1usize;
                v___x_4566_ = lean_usize_add(v_i_4560_, v___x_4565_);
                v_i_4560_ = v___x_4566_;
                v_b_4561_ = v_a_4564_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_query_x3f_4569_) == 1 {
                    v_val_4570_ = crate::leanh::lean_ctor_get(v_query_x3f_4569_, 0);
                    crate::leanh::lean_inc(v_val_4570_);
                    crate::leanh::lean_dec_ref_known(v_query_x3f_4569_, 1);
                    v___x_4571_ = lean_array_push(v_b_4561_, v_val_4570_);
                    v_a_4564_ = v___x_4571_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_query_x3f_4569_);
                    v_a_4564_ = v_b_4561_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4589_ = l_Lean_Server_RequestError_ofIoError(v_a_4585_);
                if v_isShared_4588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4587_, 0, v___x_4589_);
                    v___x_4591_ = v___x_4587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
                    v___x_4591_ = v_reuseFailAlloc_4592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4591_;
            }
            5 => {
                v___x_4605_ = l_Lean_Server_RequestError_ofIoError(v_a_4601_);
                if v_isShared_4604_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4603_, 0, v___x_4605_);
                    v___x_4607_ = v___x_4603_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
                    v___x_4607_ = v_reuseFailAlloc_4608_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(
    mut v_doc_4610_: *mut crate::leanh::LeanObject,
    mut v_as_4611_: *mut crate::leanh::LeanObject,
    mut v_sz_4612_: *mut crate::leanh::LeanObject,
    mut v_i_4613_: *mut crate::leanh::LeanObject,
    mut v_b_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4616_: usize = 0;
    let mut v_i_boxed_4617_: usize = 0;
    let mut v_res_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4616_ = crate::leanh::lean_unbox_usize(v_sz_4612_);
    crate::leanh::lean_dec(v_sz_4612_);
    v_i_boxed_4617_ = crate::leanh::lean_unbox_usize(v_i_4613_);
    crate::leanh::lean_dec(v_i_4613_);
    v_res_4618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4610_, v_as_4611_, v_sz_boxed_4616_, v_i_boxed_4617_, v_b_4614_);
    crate::leanh::lean_dec_ref(v_as_4611_);
    return v_res_4618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(
    mut v_doc_4619_: *mut crate::leanh::LeanObject,
    mut v_as_4620_: *mut crate::leanh::LeanObject,
    mut v_sz_4621_: usize,
    mut v_i_4622_: usize,
    mut v_b_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: usize = 0;
    let mut v___x_4637_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4626_ = lean_usize_dec_lt(v_i_4622_, v_sz_4621_);
                if v___x_4626_ == 0 {
                    crate::leanh::lean_dec_ref(v_doc_4619_);
                    v___x_4627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4627_, 0, v_b_4623_);
                    return v___x_4627_;
                } else {
                    v_a_4628_ = lean_array_uget_borrowed(v_as_4620_, v_i_4622_);
                    v_sz_4629_ = lean_array_size(v_a_4628_);
                    v___x_4630_ = 0usize;
                    crate::leanh::lean_inc_ref(v_doc_4619_);
                    v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4619_, v_a_4628_, v_sz_4629_, v___x_4630_, v_b_4623_);
                    if crate::leanh::lean_obj_tag(v___x_4631_) == 0 {
                        v_a_4632_ = crate::leanh::lean_ctor_get(v___x_4631_, 0);
                        crate::leanh::lean_inc(v_a_4632_);
                        v___x_4633_ = lean_array_get_size(v_a_4632_);
                        v___x_4634_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4635_ = lean_nat_dec_eq(v___x_4633_, v___x_4634_);
                        if v___x_4635_ == 0 {
                            crate::leanh::lean_dec(v_a_4632_);
                            crate::leanh::lean_dec_ref(v_doc_4619_);
                            return v___x_4631_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4631_, 1);
                            v___x_4636_ = 1usize;
                            v___x_4637_ = lean_usize_add(v_i_4622_, v___x_4636_);
                            v_i_4622_ = v___x_4637_;
                            v_b_4623_ = v_a_4632_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_doc_4619_);
                        return v___x_4631_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(
    mut v_doc_4639_: *mut crate::leanh::LeanObject,
    mut v_as_4640_: *mut crate::leanh::LeanObject,
    mut v_sz_4641_: *mut crate::leanh::LeanObject,
    mut v_i_4642_: *mut crate::leanh::LeanObject,
    mut v_b_4643_: *mut crate::leanh::LeanObject,
    mut v___y_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4646_: usize = 0;
    let mut v_i_boxed_4647_: usize = 0;
    let mut v_res_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4646_ = crate::leanh::lean_unbox_usize(v_sz_4641_);
    crate::leanh::lean_dec(v_sz_4641_);
    v_i_boxed_4647_ = crate::leanh::lean_unbox_usize(v_i_4642_);
    crate::leanh::lean_dec(v_i_4642_);
    v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4639_, v_as_4640_, v_sz_boxed_4646_, v_i_boxed_4647_, v_b_4643_, v___y_4644_);
    crate::leanh::lean_dec_ref(v___y_4644_);
    crate::leanh::lean_dec_ref(v_as_4640_);
    return v_res_4648_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries(
    mut v_doc_4651_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_4655_ = crate::leanh::lean_ctor_get(v_doc_4651_, 0);
    v___x_4656_ = 1;
    crate::leanh::lean_inc(v_requestedPos_4652_);
    crate::leanh::lean_inc_ref(v_doc_4651_);
    v___x_4657_ =
        l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_4651_, v_requestedPos_4652_, v___x_4656_);
    v___x_4658_ = lean_task_get_own(v___x_4657_);
    if crate::leanh::lean_obj_tag(v___x_4658_) == 1 {
        let mut v_val_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_meta_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_queries_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4667_: usize = 0;
        let mut v___x_4668_: usize = 0;
        let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4659_ = crate::leanh::lean_ctor_get(v___x_4658_, 0);
        crate::leanh::lean_inc(v_val_4659_);
        crate::leanh::lean_dec_ref_known(v___x_4658_, 1);
        v_meta_4660_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4655_, 0);
        v_fst_4661_ = crate::leanh::lean_ctor_get(v_val_4659_, 0);
        crate::leanh::lean_inc(v_fst_4661_);
        v_snd_4662_ = crate::leanh::lean_ctor_get(v_val_4659_, 1);
        crate::leanh::lean_inc(v_snd_4662_);
        crate::leanh::lean_dec(v_val_4659_);
        v_text_4663_ = crate::leanh::lean_ctor_get(v_meta_4660_, 3);
        crate::leanh::lean_inc_ref(v_text_4663_);
        v___x_4664_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
            v_text_4663_,
            v_requestedPos_4652_,
            v_fst_4661_,
            v_snd_4662_,
        );
        v_fst_4665_ = crate::leanh::lean_ctor_get(v___x_4664_, 0);
        crate::leanh::lean_inc(v_fst_4665_);
        crate::leanh::lean_dec_ref(v___x_4664_);
        v_queries_4666_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v_sz_4667_ = lean_array_size(v_fst_4665_);
        v___x_4668_ = 0usize;
        v___x_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4651_, v_fst_4665_, v_sz_4667_, v___x_4668_, v_queries_4666_, v_a_4653_);
        crate::leanh::lean_dec(v_fst_4665_);
        return v___x_4669_;
    } else {
        let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4658_);
        crate::leanh::lean_dec(v_requestedPos_4652_);
        crate::leanh::lean_dec_ref(v_doc_4651_);
        v___x_4670_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v___x_4671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4671_, 0, v___x_4670_);
        return v___x_4671_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries___boxed(
    mut v_doc_4672_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_4673_: *mut crate::leanh::LeanObject,
    mut v_a_4674_: *mut crate::leanh::LeanObject,
    mut v_a_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ =
        l_Lean_Server_FileWorker_computeQueries(v_doc_4672_, v_requestedPos_4673_, v_a_4674_);
    crate::leanh::lean_dec_ref(v_a_4674_);
    return v_res_4676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(
    mut v_doc_4677_: *mut crate::leanh::LeanObject,
    mut v_as_4678_: *mut crate::leanh::LeanObject,
    mut v_sz_4679_: usize,
    mut v_i_4680_: usize,
    mut v_b_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4677_, v_as_4678_, v_sz_4679_, v_i_4680_, v_b_4681_);
    return v___x_4684_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(
    mut v_doc_4685_: *mut crate::leanh::LeanObject,
    mut v_as_4686_: *mut crate::leanh::LeanObject,
    mut v_sz_4687_: *mut crate::leanh::LeanObject,
    mut v_i_4688_: *mut crate::leanh::LeanObject,
    mut v_b_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4692_: usize = 0;
    let mut v_i_boxed_4693_: usize = 0;
    let mut v_res_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4692_ = crate::leanh::lean_unbox_usize(v_sz_4687_);
    crate::leanh::lean_dec(v_sz_4687_);
    v_i_boxed_4693_ = crate::leanh::lean_unbox_usize(v_i_4688_);
    crate::leanh::lean_dec(v_i_4688_);
    v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_4685_, v_as_4686_, v_sz_boxed_4692_, v_i_boxed_4693_, v_b_4689_, v___y_4690_);
    crate::leanh::lean_dec_ref(v___y_4690_);
    crate::leanh::lean_dec_ref(v_as_4686_);
    return v_res_4694_;
}
pub unsafe fn l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
    mut v_params_4703_: *mut crate::leanh::LeanObject,
    mut v_name_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4706_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4706_, 0, v_params_4703_);
    crate::leanh::lean_ctor_set(v___x_4706_, 1, v_name_4704_);
    crate::leanh::lean_ctor_set(v___x_4706_, 2, v___x_4705_);
    return v___x_4706_;
}
pub unsafe fn l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
    mut v_params_4708_: *mut crate::leanh::LeanObject,
    mut v_kind_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = crate::leanh::lean_box(0);
    v___x_4711_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0;
    v___x_4712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4712_, 0, v_kind_4709_);
    v___x_4713_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
    v___x_4714_ =
        l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_4708_, v___x_4713_);
    v___x_4715_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4714_);
    v___x_4716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4716_, 0, v___x_4715_);
    v___x_4717_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4717_, 0, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 1, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 2, v___x_4711_);
    crate::leanh::lean_ctor_set(v___x_4717_, 3, v___x_4712_);
    crate::leanh::lean_ctor_set(v___x_4717_, 4, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 5, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 6, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 7, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 8, v___x_4710_);
    crate::leanh::lean_ctor_set(v___x_4717_, 9, v___x_4716_);
    return v___x_4717_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(
    mut v_ctx_4722_: *mut crate::leanh::LeanObject,
    mut v_mod_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toCommandContextInfo_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: u8 = 0;
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toCommandContextInfo_4724_ = crate::leanh::lean_ctor_get(v_ctx_4722_, 0);
    crate::leanh::lean_inc_ref(v_toCommandContextInfo_4724_);
    v_parentDecl_x3f_4725_ = crate::leanh::lean_ctor_get(v_ctx_4722_, 1);
    crate::leanh::lean_inc(v_parentDecl_x3f_4725_);
    crate::leanh::lean_dec_ref(v_ctx_4722_);
    v___x_4726_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0;
    v___x_4727_ = 1;
    v___x_4728_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4723_, v___x_4727_);
    v___x_4729_ = lean_string_append(v___x_4726_, v___x_4728_);
    crate::leanh::lean_dec_ref(v___x_4728_);
    v___x_4730_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
    v_text_4731_ = lean_string_append(v___x_4729_, v___x_4730_);
    if crate::leanh::lean_obj_tag(v_parentDecl_x3f_4725_) == 1 {
        let mut v_val_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: u8 = 0;
        v_val_4732_ = crate::leanh::lean_ctor_get(v_parentDecl_x3f_4725_, 0);
        crate::leanh::lean_inc_n(v_val_4732_, 2);
        crate::leanh::lean_dec_ref_known(v_parentDecl_x3f_4725_, 1);
        v_env_4733_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_4724_, 0);
        crate::leanh::lean_inc_ref_n(v_env_4733_, 2);
        crate::leanh::lean_dec_ref(v_toCommandContextInfo_4724_);
        v___x_4734_ = l_Lean_isMarkedMeta(v_env_4733_, v_val_4732_);
        if v___x_4734_ == 0 {
            let mut v_isExporting_4735_: u8 = 0;
            crate::leanh::lean_dec(v_val_4732_);
            v_isExporting_4735_ = crate::leanh::lean_ctor_get_uint8(
                v_env_4733_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
            );
            crate::leanh::lean_dec_ref(v_env_4733_);
            if v_isExporting_4735_ == 0 {
                return v_text_4731_;
            } else {
                let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_text_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4736_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                v_text_4737_ = lean_string_append(v___x_4736_, v_text_4731_);
                crate::leanh::lean_dec_ref(v_text_4731_);
                return v_text_4737_;
            }
        } else {
            let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_text_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4740_: u8 = 0;
            crate::leanh::lean_dec_ref(v_env_4733_);
            v___x_4738_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3;
            v_text_4739_ = lean_string_append(v___x_4738_, v_text_4731_);
            crate::leanh::lean_dec_ref(v_text_4731_);
            v___x_4740_ = l_Lean_isPrivateName(v_val_4732_);
            crate::leanh::lean_dec(v_val_4732_);
            if v___x_4740_ == 0 {
                if v___x_4734_ == 0 {
                    return v_text_4739_;
                } else {
                    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_text_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_4741_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                    v_text_4742_ = lean_string_append(v___x_4741_, v_text_4739_);
                    crate::leanh::lean_dec_ref(v_text_4739_);
                    return v_text_4742_;
                }
            } else {
                return v_text_4739_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_parentDecl_x3f_4725_);
        crate::leanh::lean_dec_ref(v_toCommandContextInfo_4724_);
        return v_text_4731_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(
    mut v_x_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_response_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_code_4764_: u8 = 0;
    let mut v_message_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4744_) == 0 {
                    v_response_4745_ = crate::leanh::lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4763_ = (!crate::leanh::lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4747_ = v_x_4744_;
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_response_4745_);
                        crate::leanh::lean_dec(v_x_4744_);
                        v___x_4747_ = crate::leanh::lean_box(0);
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_code_4764_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_4744_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_message_4765_ = crate::leanh::lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4772_ = (!crate::leanh::lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4772_ == 0 {
                        v___x_4767_ = v_x_4744_;
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_message_4765_);
                        crate::leanh::lean_dec(v_x_4744_);
                        v___x_4767_ = crate::leanh::lean_box(0);
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_response_4745_);
                v___x_4749_ =
                    l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_4745_);
                if crate::leanh::lean_obj_tag(v___x_4749_) == 0 {
                    crate::leanh::lean_del_object(v___x_4747_);
                    v_a_4750_ = crate::leanh::lean_ctor_get(v___x_4749_, 0);
                    crate::leanh::lean_inc(v_a_4750_);
                    crate::leanh::lean_dec_ref_known(v___x_4749_, 1);
                    v___x_4751_ = 0;
                    v___x_4752_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0;
                    v___x_4753_ = l_Lean_Json_compress(v_response_4745_);
                    v___x_4754_ = lean_string_append(v___x_4752_, v___x_4753_);
                    crate::leanh::lean_dec_ref(v___x_4753_);
                    v___x_4755_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
                    v___x_4756_ = lean_string_append(v___x_4754_, v___x_4755_);
                    v___x_4757_ = lean_string_append(v___x_4756_, v_a_4750_);
                    crate::leanh::lean_dec(v_a_4750_);
                    v___x_4758_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4758_, 0, v___x_4757_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4758_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4751_,
                    );
                    return v___x_4758_;
                } else {
                    crate::leanh::lean_dec(v_response_4745_);
                    v_a_4759_ = crate::leanh::lean_ctor_get(v___x_4749_, 0);
                    crate::leanh::lean_inc(v_a_4759_);
                    crate::leanh::lean_dec_ref_known(v___x_4749_, 1);
                    if v_isShared_4748_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4747_, 0, v_a_4759_);
                        v___x_4761_ = v___x_4747_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4759_);
                        v___x_4761_ = v_reuseFailAlloc_4762_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4761_;
            }
            3 => {
                if v_isShared_4768_ == 0 {
                    v___x_4770_ = v___x_4767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_message_4765_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_code_4764_,
                    );
                    v___x_4770_ = v_reuseFailAlloc_4771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(
    mut v_method_4774_: *mut crate::leanh::LeanObject,
    mut v_param_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverRequestEmitter_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverRequestEmitter_4778_ = crate::leanh::lean_ctor_get(v_a_4776_, 5);
    v___x_4779_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_4775_);
    crate::leanh::lean_inc_ref(v_serverRequestEmitter_4778_);
    v___x_4780_ = crate::leanh::lean_apply_3(
        v_serverRequestEmitter_4778_,
        v_method_4774_,
        v___x_4779_,
        crate::leanh::lean_box(0),
    );
    v___f_4781_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0;
    v___x_4782_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4781_, v___x_4780_);
    v___x_4783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4783_, 0, v___x_4782_);
    return v___x_4783_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(
    mut v_method_4784_: *mut crate::leanh::LeanObject,
    mut v_param_4785_: *mut crate::leanh::LeanObject,
    mut v_a_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4788_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_4784_, v_param_4785_, v_a_4786_);
    crate::leanh::lean_dec_ref(v_a_4786_);
    return v_res_4788_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(
    mut v_val_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4790_, 0, v_val_4789_);
    return v___x_4790_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(
    mut v_val_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4792_, 0, v_val_4791_);
    return v___x_4792_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(
    mut v_sz_4793_: usize,
    mut v_i_4794_: usize,
    mut v_bs_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: u8 = 0;
    let mut v_v_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanModuleQuery_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: usize = 0;
    let mut v___x_4802_: usize = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
                if v___x_4796_ == 0 {
                    return v_bs_4795_;
                } else {
                    v_v_4797_ = lean_array_uget_borrowed(v_bs_4795_, v_i_4794_);
                    v_toLeanModuleQuery_4798_ = crate::leanh::lean_ctor_get(v_v_4797_, 0);
                    crate::leanh::lean_inc_ref(v_toLeanModuleQuery_4798_);
                    v___x_4799_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4800_ = lean_array_uset(v_bs_4795_, v_i_4794_, v___x_4799_);
                    v___x_4801_ = 1usize;
                    v___x_4802_ = lean_usize_add(v_i_4794_, v___x_4801_);
                    v___x_4803_ =
                        lean_array_uset(v_bs_x27_4800_, v_i_4794_, v_toLeanModuleQuery_4798_);
                    v_i_4794_ = v___x_4802_;
                    v_bs_4795_ = v___x_4803_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(
    mut v_sz_4805_: *mut crate::leanh::LeanObject,
    mut v_i_4806_: *mut crate::leanh::LeanObject,
    mut v_bs_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4808_: usize = 0;
    let mut v_i_boxed_4809_: usize = 0;
    let mut v_res_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4808_ = crate::leanh::lean_unbox_usize(v_sz_4805_);
    crate::leanh::lean_dec(v_sz_4805_);
    v_i_boxed_4809_ = crate::leanh::lean_unbox_usize(v_i_4806_);
    crate::leanh::lean_dec(v_i_4806_);
    v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_4808_, v_i_boxed_4809_, v_bs_4807_);
    return v_res_4810_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(
    mut v_a_4814_: *mut crate::leanh::LeanObject,
    mut v_kind_4815_: *mut crate::leanh::LeanObject,
    mut v___x_4816_: *mut crate::leanh::LeanObject,
    mut v_params_4817_: *mut crate::leanh::LeanObject,
    mut v___x_4818_: *mut crate::leanh::LeanObject,
    mut v___x_4819_: *mut crate::leanh::LeanObject,
    mut v_as_4820_: *mut crate::leanh::LeanObject,
    mut v_sz_4821_: usize,
    mut v_i_4822_: usize,
    mut v_b_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_4835_: u8 = 0;
    let mut v_fst_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v_ctx_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4844_: u8 = 0;
    let mut v___y_4845_: u8 = 0;
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullName_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut v_fullName_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u8 = 0;
    let mut v___y_4924_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v___x_4927_: u8 = 0;
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4830_ = lean_usize_dec_lt(v_i_4822_, v_sz_4821_);
                if v___x_4830_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4818_);
                    crate::leanh::lean_dec_ref(v_params_4817_);
                    crate::leanh::lean_dec_ref(v___x_4816_);
                    crate::leanh::lean_dec_ref(v_kind_4815_);
                    crate::leanh::lean_dec_ref(v_a_4814_);
                    v___x_4831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4831_, 0, v_b_4823_);
                    return v___x_4831_;
                } else {
                    v_a_4832_ = lean_array_uget_borrowed(v_as_4820_, v_i_4822_);
                    v_module_4833_ = crate::leanh::lean_ctor_get(v_a_4832_, 0);
                    v_decl_4834_ = crate::leanh::lean_ctor_get(v_a_4832_, 1);
                    v_isExactMatch_4835_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4832_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_fst_4836_ = crate::leanh::lean_ctor_get(v_b_4823_, 0);
                    v_snd_4837_ = crate::leanh::lean_ctor_get(v_b_4823_, 1);
                    v_isSharedCheck_4928_ = (!crate::leanh::lean_is_exclusive(v_b_4823_)) as u8;
                    if v_isSharedCheck_4928_ == 0 {
                        v___x_4839_ = v_b_4823_;
                        v_isShared_4840_ = v_isSharedCheck_4928_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4837_);
                        crate::leanh::lean_inc(v_fst_4836_);
                        crate::leanh::lean_dec(v_b_4823_);
                        v___x_4839_ = crate::leanh::lean_box(0);
                        v_isShared_4840_ = v_isSharedCheck_4928_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4827_ = 1usize;
                v___x_4828_ = lean_usize_add(v_i_4822_, v___x_4827_);
                v_i_4822_ = v___x_4828_;
                v_b_4823_ = v_a_4826_;
                state = 0;
                continue;
            }
            2 => {
                v_ctx_4841_ = crate::leanh::lean_ctor_get(v_a_4814_, 1);
                v_determineInsertion_4842_ = crate::leanh::lean_ctor_get(v_a_4814_, 2);
                v_toCommandContextInfo_4919_ = crate::leanh::lean_ctor_get(v_ctx_4841_, 0);
                v_env_4920_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_4919_, 0);
                v___x_4921_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4922_ = lean_nat_dec_eq(v___x_4819_, v___x_4921_);
                crate::leanh::lean_inc(v_decl_4834_);
                crate::leanh::lean_inc_ref(v_env_4920_);
                v___x_4927_ = l_Lean_Environment_contains(v_env_4920_, v_decl_4834_, v___x_4830_);
                if v___x_4927_ == 0 {
                    v___y_4924_ = v___x_4830_;
                    state = 12;
                    continue;
                } else {
                    v___y_4924_ = v___x_4922_;
                    state = 12;
                    continue;
                }
            }
            3 => {
                if v___y_4845_ == 0 {
                    crate::leanh::lean_inc_ref(v_determineInsertion_4842_);
                    crate::leanh::lean_inc(v_decl_4834_);
                    v___x_4846_ =
                        crate::leanh::lean_apply_1(v_determineInsertion_4842_, v_decl_4834_);
                    if v___y_4844_ == 0 {
                        v_fullName_4847_ = crate::leanh::lean_ctor_get(v___x_4846_, 0);
                        v_edit_4848_ = crate::leanh::lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4875_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4875_ == 0 {
                            v___x_4850_ = v___x_4846_;
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_edit_4848_);
                            crate::leanh::lean_inc(v_fullName_4847_);
                            crate::leanh::lean_dec(v___x_4846_);
                            v___x_4850_ = crate::leanh::lean_box(0);
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_fullName_4876_ = crate::leanh::lean_ctor_get(v___x_4846_, 0);
                        v_edit_4877_ = crate::leanh::lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4915_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4915_ == 0 {
                            v___x_4879_ = v___x_4846_;
                            v_isShared_4880_ = v_isSharedCheck_4915_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_edit_4877_);
                            crate::leanh::lean_inc(v_fullName_4876_);
                            crate::leanh::lean_dec(v___x_4846_);
                            v___x_4879_ = crate::leanh::lean_box(0);
                            v_isShared_4880_ = v_isSharedCheck_4915_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_4840_ == 0 {
                        v___x_4917_ = v___x_4839_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4918_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_fst_4836_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_snd_4837_);
                        v___x_4917_ = v_reuseFailAlloc_4918_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4852_ = crate::leanh::lean_box(0);
                v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
                v___x_4854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4847_,
                    v___x_4830_,
                );
                v___x_4855_ = lean_string_append(v___x_4853_, v___x_4854_);
                crate::leanh::lean_dec_ref(v___x_4854_);
                crate::leanh::lean_inc_ref(v_kind_4815_);
                v___x_4856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4856_, 0, v_kind_4815_);
                crate::leanh::lean_inc_ref(v___x_4816_);
                v___x_4857_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                v___x_4858_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4859_ = lean_mk_empty_array_with_capacity(v___x_4858_);
                v___x_4860_ = lean_array_push(v___x_4859_, v_edit_4848_);
                if v_isShared_4851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4860_);
                    crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4857_);
                    v___x_4862_ = v___x_4850_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4860_);
                    v___x_4862_ = v_reuseFailAlloc_4874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4863_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4862_);
                v___x_4864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4864_, 0, v___x_4863_);
                v___x_4865_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                crate::leanh::lean_inc_ref(v_params_4817_);
                v___x_4866_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4865_,
                );
                v___x_4867_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4866_);
                v___x_4868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4867_);
                v___x_4869_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 1, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 2, v___x_4855_);
                crate::leanh::lean_ctor_set(v___x_4869_, 3, v___x_4856_);
                crate::leanh::lean_ctor_set(v___x_4869_, 4, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 5, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 6, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 7, v___x_4864_);
                crate::leanh::lean_ctor_set(v___x_4869_, 8, v___x_4852_);
                crate::leanh::lean_ctor_set(v___x_4869_, 9, v___x_4868_);
                v___x_4870_ = lean_array_push(v_fst_4836_, v___x_4869_);
                if v_isShared_4840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4870_);
                    v___x_4872_ = v___x_4839_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 1, v_snd_4837_);
                    v___x_4872_ = v_reuseFailAlloc_4873_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4826_ = v___x_4872_;
                state = 1;
                continue;
            }
            7 => {
                v___x_4881_ = crate::leanh::lean_box(0);
                v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
                v___x_4883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4876_,
                    v___y_4844_,
                );
                v___x_4884_ = lean_string_append(v___x_4882_, v___x_4883_);
                crate::leanh::lean_dec_ref(v___x_4883_);
                v___x_4885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
                v___x_4886_ = lean_string_append(v___x_4884_, v___x_4885_);
                crate::leanh::lean_inc_n(v_module_4833_, 2);
                v___x_4887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_module_4833_,
                    v___y_4844_,
                );
                v___x_4888_ = lean_string_append(v___x_4886_, v___x_4887_);
                crate::leanh::lean_dec_ref(v___x_4887_);
                crate::leanh::lean_inc_ref(v_kind_4815_);
                v___x_4889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4889_, 0, v_kind_4815_);
                crate::leanh::lean_inc_ref(v___x_4816_);
                v___x_4890_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                crate::leanh::lean_inc_ref(v_ctx_4841_);
                v___x_4891_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_4841_, v_module_4833_);
                crate::leanh::lean_inc_ref(v___x_4818_);
                v___x_4892_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4892_, 0, v___x_4818_);
                crate::leanh::lean_ctor_set(v___x_4892_, 1, v___x_4891_);
                crate::leanh::lean_ctor_set(v___x_4892_, 2, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4892_, 3, v___x_4881_);
                v___x_4893_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4894_ = lean_mk_empty_array_with_capacity(v___x_4893_);
                v___x_4895_ = lean_array_push(v___x_4894_, v___x_4892_);
                v___x_4896_ = lean_array_push(v___x_4895_, v_edit_4877_);
                if v_isShared_4880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4879_, 1, v___x_4896_);
                    crate::leanh::lean_ctor_set(v___x_4879_, 0, v___x_4890_);
                    v___x_4898_ = v___x_4879_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4896_);
                    v___x_4898_ = v_reuseFailAlloc_4914_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4899_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4898_);
                v___x_4900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4899_);
                v___x_4901_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                crate::leanh::lean_inc_ref(v_params_4817_);
                v___x_4902_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4901_,
                );
                v___x_4903_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4902_);
                v___x_4904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
                v___x_4905_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 1, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 2, v___x_4888_);
                crate::leanh::lean_ctor_set(v___x_4905_, 3, v___x_4889_);
                crate::leanh::lean_ctor_set(v___x_4905_, 4, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 5, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 6, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 7, v___x_4900_);
                crate::leanh::lean_ctor_set(v___x_4905_, 8, v___x_4881_);
                crate::leanh::lean_ctor_set(v___x_4905_, 9, v___x_4904_);
                v___x_4906_ = lean_array_push(v_fst_4836_, v___x_4905_);
                if v_isExactMatch_4835_ == 0 {
                    if v_isShared_4840_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4908_ = v___x_4839_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4909_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4906_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_snd_4837_);
                        v___x_4908_ = v_reuseFailAlloc_4909_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4837_);
                    v___x_4910_ = crate::leanh::lean_box((v___x_4830_) as usize);
                    if v_isShared_4840_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4839_, 1, v___x_4910_);
                        crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4912_ = v___x_4839_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4906_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 1, v___x_4910_);
                        v___x_4912_ = v_reuseFailAlloc_4913_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                v_a_4826_ = v___x_4908_;
                state = 1;
                continue;
            }
            10 => {
                v_a_4826_ = v___x_4912_;
                state = 1;
                continue;
            }
            11 => {
                v_a_4826_ = v___x_4917_;
                state = 1;
                continue;
            }
            12 => {
                if v___y_4924_ == 0 {
                    v___y_4844_ = v___y_4924_;
                    v___y_4845_ = v___x_4922_;
                    state = 3;
                    continue;
                } else {
                    v___x_4925_ = l_Lean_Environment_mainModule(v_env_4920_);
                    v___x_4926_ = lean_name_eq(v_module_4833_, v___x_4925_);
                    crate::leanh::lean_dec(v___x_4925_);
                    v___y_4844_ = v___y_4924_;
                    v___y_4845_ = v___x_4926_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_kind_4930_: *mut crate::leanh::LeanObject,
    mut v___x_4931_: *mut crate::leanh::LeanObject,
    mut v_params_4932_: *mut crate::leanh::LeanObject,
    mut v___x_4933_: *mut crate::leanh::LeanObject,
    mut v___x_4934_: *mut crate::leanh::LeanObject,
    mut v_as_4935_: *mut crate::leanh::LeanObject,
    mut v_sz_4936_: *mut crate::leanh::LeanObject,
    mut v_i_4937_: *mut crate::leanh::LeanObject,
    mut v_b_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4940_: usize = 0;
    let mut v_i_boxed_4941_: usize = 0;
    let mut v_res_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4940_ = crate::leanh::lean_unbox_usize(v_sz_4936_);
    crate::leanh::lean_dec(v_sz_4936_);
    v_i_boxed_4941_ = crate::leanh::lean_unbox_usize(v_i_4937_);
    crate::leanh::lean_dec(v_i_4937_);
    v_res_4942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4929_, v_kind_4930_, v___x_4931_, v_params_4932_, v___x_4933_, v___x_4934_, v_as_4935_, v_sz_boxed_4940_, v_i_boxed_4941_, v_b_4938_);
    crate::leanh::lean_dec_ref(v_as_4935_);
    crate::leanh::lean_dec(v___x_4934_);
    return v_res_4942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(
    mut v_kind_4943_: *mut crate::leanh::LeanObject,
    mut v___x_4944_: *mut crate::leanh::LeanObject,
    mut v_params_4945_: *mut crate::leanh::LeanObject,
    mut v___x_4946_: *mut crate::leanh::LeanObject,
    mut v___x_4947_: *mut crate::leanh::LeanObject,
    mut v_as_4948_: *mut crate::leanh::LeanObject,
    mut v_sz_4949_: usize,
    mut v_i_4950_: usize,
    mut v_b_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v_fst_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v_array_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: u8 = 0;
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_a_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4984_: usize = 0;
    let mut v___x_4985_: usize = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v_reuseFailAlloc_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_a_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_reuseFailAlloc_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut v_unused_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v_unused_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4954_ = lean_usize_dec_lt(v_i_4950_, v_sz_4949_);
                if v___x_4954_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4946_);
                    crate::leanh::lean_dec_ref(v_params_4945_);
                    crate::leanh::lean_dec_ref(v___x_4944_);
                    crate::leanh::lean_dec_ref(v_kind_4943_);
                    v___x_4955_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4955_, 0, v_b_4951_);
                    return v___x_4955_;
                } else {
                    v_snd_4956_ = crate::leanh::lean_ctor_get(v_b_4951_, 1);
                    crate::leanh::lean_inc(v_snd_4956_);
                    v_snd_4957_ = crate::leanh::lean_ctor_get(v_snd_4956_, 1);
                    crate::leanh::lean_inc(v_snd_4957_);
                    v_fst_4958_ = crate::leanh::lean_ctor_get(v_b_4951_, 0);
                    v_isSharedCheck_5023_ = (!crate::leanh::lean_is_exclusive(v_b_4951_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v_unused_5024_ = crate::leanh::lean_ctor_get(v_b_4951_, 1);
                        crate::leanh::lean_dec(v_unused_5024_);
                        v___x_4960_ = v_b_4951_;
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4958_);
                        crate::leanh::lean_dec(v_b_4951_);
                        v___x_4960_ = crate::leanh::lean_box(0);
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4962_ = crate::leanh::lean_ctor_get(v_snd_4956_, 0);
                v_isSharedCheck_5021_ = (!crate::leanh::lean_is_exclusive(v_snd_4956_)) as u8;
                if v_isSharedCheck_5021_ == 0 {
                    v_unused_5022_ = crate::leanh::lean_ctor_get(v_snd_4956_, 1);
                    crate::leanh::lean_dec(v_unused_5022_);
                    v___x_4964_ = v_snd_4956_;
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4962_);
                    crate::leanh::lean_dec(v_snd_4956_);
                    v___x_4964_ = crate::leanh::lean_box(0);
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_array_4966_ = crate::leanh::lean_ctor_get(v_snd_4957_, 0);
                v_start_4967_ = crate::leanh::lean_ctor_get(v_snd_4957_, 1);
                v_stop_4968_ = crate::leanh::lean_ctor_get(v_snd_4957_, 2);
                v___x_4969_ = lean_nat_dec_lt(v_start_4967_, v_stop_4968_);
                if v___x_4969_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4946_);
                    crate::leanh::lean_dec_ref(v_params_4945_);
                    crate::leanh::lean_dec_ref(v___x_4944_);
                    crate::leanh::lean_dec_ref(v_kind_4943_);
                    if v_isShared_4965_ == 0 {
                        v___x_4971_ = v___x_4964_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_fst_4962_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 1, v_snd_4957_);
                        v___x_4971_ = v_reuseFailAlloc_4976_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_4968_);
                    crate::leanh::lean_inc(v_start_4967_);
                    crate::leanh::lean_inc_ref(v_array_4966_);
                    v_isSharedCheck_5017_ = (!crate::leanh::lean_is_exclusive(v_snd_4957_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = crate::leanh::lean_ctor_get(v_snd_4957_, 2);
                        crate::leanh::lean_dec(v_unused_5018_);
                        v_unused_5019_ = crate::leanh::lean_ctor_get(v_snd_4957_, 1);
                        crate::leanh::lean_dec(v_unused_5019_);
                        v_unused_5020_ = crate::leanh::lean_ctor_get(v_snd_4957_, 0);
                        crate::leanh::lean_dec(v_unused_5020_);
                        v___x_4978_ = v_snd_4957_;
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_4957_);
                        v___x_4978_ = crate::leanh::lean_box(0);
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4960_, 1, v___x_4971_);
                    v___x_4973_ = v___x_4960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_fst_4958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4971_);
                    v___x_4973_ = v_reuseFailAlloc_4975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4974_, 0, v___x_4973_);
                return v___x_4974_;
            }
            5 => {
                v_a_4980_ = lean_array_uget_borrowed(v_as_4948_, v_i_4950_);
                v___x_4981_ = lean_array_fget_borrowed(v_array_4966_, v_start_4967_);
                if v_isShared_4965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4964_, 1, v_fst_4962_);
                    crate::leanh::lean_ctor_set(v___x_4964_, 0, v_fst_4958_);
                    v___x_4983_ = v___x_4964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_fst_4958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_fst_4962_);
                    v___x_4983_ = v_reuseFailAlloc_5016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_sz_4984_ = lean_array_size(v___x_4981_);
                v___x_4985_ = 0usize;
                crate::leanh::lean_inc_ref(v___x_4946_);
                crate::leanh::lean_inc_ref(v_params_4945_);
                crate::leanh::lean_inc_ref(v___x_4944_);
                crate::leanh::lean_inc_ref(v_kind_4943_);
                crate::leanh::lean_inc(v_a_4980_);
                v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4980_, v_kind_4943_, v___x_4944_, v_params_4945_, v___x_4946_, v___x_4947_, v___x_4981_, v_sz_4984_, v___x_4985_, v___x_4983_);
                if crate::leanh::lean_obj_tag(v___x_4986_) == 0 {
                    v_a_4987_ = crate::leanh::lean_ctor_get(v___x_4986_, 0);
                    crate::leanh::lean_inc(v_a_4987_);
                    crate::leanh::lean_dec_ref_known(v___x_4986_, 1);
                    v_fst_4988_ = crate::leanh::lean_ctor_get(v_a_4987_, 0);
                    v_snd_4989_ = crate::leanh::lean_ctor_get(v_a_4987_, 1);
                    v_isSharedCheck_5007_ = (!crate::leanh::lean_is_exclusive(v_a_4987_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_4991_ = v_a_4987_;
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4989_);
                        crate::leanh::lean_inc(v_fst_4988_);
                        crate::leanh::lean_dec(v_a_4987_);
                        v___x_4991_ = crate::leanh::lean_box(0);
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4978_);
                    crate::leanh::lean_dec(v_stop_4968_);
                    crate::leanh::lean_dec(v_start_4967_);
                    crate::leanh::lean_dec_ref(v_array_4966_);
                    crate::leanh::lean_del_object(v___x_4960_);
                    crate::leanh::lean_dec_ref(v___x_4946_);
                    crate::leanh::lean_dec_ref(v_params_4945_);
                    crate::leanh::lean_dec_ref(v___x_4944_);
                    crate::leanh::lean_dec_ref(v_kind_4943_);
                    v_a_5008_ = crate::leanh::lean_ctor_get(v___x_4986_, 0);
                    v_isSharedCheck_5015_ = (!crate::leanh::lean_is_exclusive(v___x_4986_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5010_ = v___x_4986_;
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5008_);
                        crate::leanh::lean_dec(v___x_4986_);
                        v___x_5010_ = crate::leanh::lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4993_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4994_ = lean_nat_add(v_start_4967_, v___x_4993_);
                crate::leanh::lean_dec(v_start_4967_);
                if v_isShared_4979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4978_, 1, v___x_4994_);
                    v___x_4996_ = v___x_4978_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_array_4966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 1, v___x_4994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 2, v_stop_4968_);
                    v___x_4996_ = v_reuseFailAlloc_5006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4991_, 1, v___x_4996_);
                    crate::leanh::lean_ctor_set(v___x_4991_, 0, v_snd_4989_);
                    v___x_4998_ = v___x_4991_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_snd_4989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_5005_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4960_, 1, v___x_4998_);
                    crate::leanh::lean_ctor_set(v___x_4960_, 0, v_fst_4988_);
                    v___x_5000_ = v___x_4960_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_fst_4988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 1, v___x_4998_);
                    v___x_5000_ = v_reuseFailAlloc_5004_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5001_ = 1usize;
                v___x_5002_ = lean_usize_add(v_i_4950_, v___x_5001_);
                v_i_4950_ = v___x_5002_;
                v_b_4951_ = v___x_5000_;
                state = 0;
                continue;
            }
            11 => {
                if v_isShared_5011_ == 0 {
                    v___x_5013_ = v___x_5010_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(
    mut v_kind_5025_: *mut crate::leanh::LeanObject,
    mut v___x_5026_: *mut crate::leanh::LeanObject,
    mut v_params_5027_: *mut crate::leanh::LeanObject,
    mut v___x_5028_: *mut crate::leanh::LeanObject,
    mut v___x_5029_: *mut crate::leanh::LeanObject,
    mut v_as_5030_: *mut crate::leanh::LeanObject,
    mut v_sz_5031_: *mut crate::leanh::LeanObject,
    mut v_i_5032_: *mut crate::leanh::LeanObject,
    mut v_b_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5036_: usize = 0;
    let mut v_i_boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5036_ = crate::leanh::lean_unbox_usize(v_sz_5031_);
    crate::leanh::lean_dec(v_sz_5031_);
    v_i_boxed_5037_ = crate::leanh::lean_unbox_usize(v_i_5032_);
    crate::leanh::lean_dec(v_i_5032_);
    v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5025_, v___x_5026_, v_params_5027_, v___x_5028_, v___x_5029_, v_as_5030_, v_sz_boxed_5036_, v_i_boxed_5037_, v_b_5033_, v___y_5034_);
    crate::leanh::lean_dec_ref(v___y_5034_);
    crate::leanh::lean_dec_ref(v_as_5030_);
    crate::leanh::lean_dec(v___x_5029_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
    mut v_id_5047_: *mut crate::leanh::LeanObject,
    mut v_params_5048_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_5049_: *mut crate::leanh::LeanObject,
    mut v_kind_5050_: *mut crate::leanh::LeanObject,
    mut v_a_5051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5059_: u8 = 0;
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: u8 = 0;
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___f_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_unused_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_val_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v_snd_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v_fst_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_initSnap_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5162_: u8 = 0;
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_unused_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_unused_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5053_ = crate::leanh::lean_ctor_get(v_a_5051_, 1);
                v_cancelTk_5054_ = crate::leanh::lean_ctor_get(v_a_5051_, 4);
                v_toEditableDocumentCore_5055_ = crate::leanh::lean_ctor_get(v_doc_5053_, 0);
                v_stop_5056_ = crate::leanh::lean_ctor_get(v_requestedRange_5049_, 1);
                v_isSharedCheck_5185_ =
                    (!crate::leanh::lean_is_exclusive(v_requestedRange_5049_)) as u8;
                if v_isSharedCheck_5185_ == 0 {
                    v_unused_5186_ = crate::leanh::lean_ctor_get(v_requestedRange_5049_, 0);
                    crate::leanh::lean_dec(v_unused_5186_);
                    v___x_5058_ = v_requestedRange_5049_;
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_5056_);
                    crate::leanh::lean_dec(v_requestedRange_5049_);
                    v___x_5058_ = crate::leanh::lean_box(0);
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_doc_5053_);
                v___x_5060_ =
                    l_Lean_Server_FileWorker_computeQueries(v_doc_5053_, v_stop_5056_, v_a_5051_);
                if crate::leanh::lean_obj_tag(v___x_5060_) == 0 {
                    v_a_5061_ = crate::leanh::lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5176_ = (!crate::leanh::lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5063_ = v___x_5060_;
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5061_);
                        crate::leanh::lean_dec(v___x_5060_);
                        v___x_5063_ = crate::leanh::lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5058_);
                    crate::leanh::lean_dec_ref(v_kind_5050_);
                    crate::leanh::lean_dec_ref(v_params_5048_);
                    crate::leanh::lean_dec(v_id_5047_);
                    v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5184_ = (!crate::leanh::lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5184_ == 0 {
                        v___x_5179_ = v___x_5060_;
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5177_);
                        crate::leanh::lean_dec(v___x_5060_);
                        v___x_5179_ = crate::leanh::lean_box(0);
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5065_ = lean_array_get_size(v_a_5061_);
                v___x_5066_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5067_ = lean_nat_dec_eq(v___x_5065_, v___x_5066_);
                if v___x_5067_ == 0 {
                    crate::leanh::lean_del_object(v___x_5063_);
                    v___x_5068_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5069_ = lean_array_size(v_a_5061_);
                    v___x_5070_ = 0usize;
                    crate::leanh::lean_inc(v_a_5061_);
                    v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5069_, v___x_5070_, v_a_5061_);
                    if v_isShared_5059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5058_, 1, v___x_5071_);
                        crate::leanh::lean_ctor_set(v___x_5058_, 0, v_id_5047_);
                        v___x_5073_ = v___x_5058_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_id_5047_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 1, v___x_5071_);
                        v___x_5073_ = v_reuseFailAlloc_5171_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5061_);
                    crate::leanh::lean_del_object(v___x_5058_);
                    crate::leanh::lean_dec_ref(v_kind_5050_);
                    crate::leanh::lean_dec_ref(v_params_5048_);
                    crate::leanh::lean_dec(v_id_5047_);
                    v___x_5172_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                    if v_isShared_5064_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5063_, 0, v___x_5172_);
                        v___x_5174_ = v___x_5063_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
                        v___x_5174_ = v_reuseFailAlloc_5175_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5074_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5068_, v___x_5073_, v_a_5051_);
                v_a_5075_ = crate::leanh::lean_ctor_get(v___x_5074_, 0);
                v_isSharedCheck_5170_ = (!crate::leanh::lean_is_exclusive(v___x_5074_)) as u8;
                if v_isSharedCheck_5170_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    v_isShared_5078_ = v_isSharedCheck_5170_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5075_);
                    crate::leanh::lean_dec(v___x_5074_);
                    v___x_5077_ = crate::leanh::lean_box(0);
                    v_isShared_5078_ = v_isSharedCheck_5170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___f_5079_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
                v___f_5080_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
                v___x_5081_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5079_, v_a_5075_);
                v___x_5082_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(
                    v_cancelTk_5054_,
                );
                v___x_5083_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5080_, v___x_5082_);
                v___x_5084_ = crate::leanh::lean_box(0);
                v___x_5085_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5085_, 0, v___x_5083_);
                crate::leanh::lean_ctor_set(v___x_5085_, 1, v___x_5084_);
                v___x_5086_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5086_, 0, v___x_5081_);
                crate::leanh::lean_ctor_set(v___x_5086_, 1, v___x_5085_);
                v___x_5087_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_5086_);
                if crate::leanh::lean_obj_tag(v___x_5087_) == 0 {
                    v_val_5108_ = crate::leanh::lean_ctor_get(v___x_5087_, 0);
                    crate::leanh::lean_inc(v_val_5108_);
                    crate::leanh::lean_dec_ref_known(v___x_5087_, 1);
                    if crate::leanh::lean_obj_tag(v_val_5108_) == 0 {
                        v_response_5109_ = crate::leanh::lean_ctor_get(v_val_5108_, 0);
                        crate::leanh::lean_inc(v_response_5109_);
                        crate::leanh::lean_dec_ref_known(v_val_5108_, 1);
                        v_initSnap_5151_ =
                            crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5055_, 1);
                        v_meta_5152_ =
                            crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5055_, 0);
                        v_stx_5153_ = crate::leanh::lean_ctor_get(v_initSnap_5151_, 3);
                        v___x_5154_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5153_, v___x_5067_);
                        if crate::leanh::lean_obj_tag(v___x_5154_) == 0 {
                            v___x_5155_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5;
                            v___y_5111_ = v___x_5155_;
                            state = 10;
                            continue;
                        } else {
                            v_val_5156_ = crate::leanh::lean_ctor_get(v___x_5154_, 0);
                            crate::leanh::lean_inc(v_val_5156_);
                            crate::leanh::lean_dec_ref_known(v___x_5154_, 1);
                            v_text_5157_ = crate::leanh::lean_ctor_get(v_meta_5152_, 3);
                            crate::leanh::lean_inc_ref(v_text_5157_);
                            v___x_5158_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5157_, v_val_5156_);
                            crate::leanh::lean_dec(v_val_5156_);
                            v_line_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
                            v_isSharedCheck_5168_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5158_)) as u8;
                            if v_isSharedCheck_5168_ == 0 {
                                v_unused_5169_ = crate::leanh::lean_ctor_get(v___x_5158_, 1);
                                crate::leanh::lean_dec(v_unused_5169_);
                                v___x_5161_ = v___x_5158_;
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_line_5159_);
                                crate::leanh::lean_dec(v___x_5158_);
                                v___x_5161_ = crate::leanh::lean_box(0);
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5108_);
                        crate::leanh::lean_del_object(v___x_5077_);
                        crate::leanh::lean_dec(v_a_5061_);
                        crate::leanh::lean_dec_ref(v_kind_5050_);
                        crate::leanh::lean_dec_ref(v_params_5048_);
                        v___y_5089_ = v_a_5051_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5087_);
                    crate::leanh::lean_del_object(v___x_5077_);
                    crate::leanh::lean_dec(v_a_5061_);
                    crate::leanh::lean_dec_ref(v_kind_5050_);
                    crate::leanh::lean_dec_ref(v_params_5048_);
                    v___y_5089_ = v_a_5051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5090_ = l_Lean_Server_RequestM_checkCancelled(v___y_5089_);
                if crate::leanh::lean_obj_tag(v___x_5090_) == 0 {
                    v_isSharedCheck_5098_ = (!crate::leanh::lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5098_ == 0 {
                        v_unused_5099_ = crate::leanh::lean_ctor_get(v___x_5090_, 0);
                        crate::leanh::lean_dec(v_unused_5099_);
                        v___x_5092_ = v___x_5090_;
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5090_);
                        v___x_5092_ = crate::leanh::lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_5100_ = crate::leanh::lean_ctor_get(v___x_5090_, 0);
                    v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5102_ = v___x_5090_;
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5100_);
                        crate::leanh::lean_dec(v___x_5090_);
                        v___x_5102_ = crate::leanh::lean_box(0);
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5094_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                if v_isShared_5093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5092_, 0, v___x_5094_);
                    v___x_5096_ = v___x_5092_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5096_;
            }
            8 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5105_;
            }
            10 => {
                crate::leanh::lean_inc_ref(v___y_5111_);
                v___x_5112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5112_, 0, v___y_5111_);
                crate::leanh::lean_ctor_set(v___x_5112_, 1, v___y_5111_);
                v___x_5113_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                v___x_5114_ = lean_array_get_size(v_response_5109_);
                v___x_5115_ = lean_nat_dec_lt(v___x_5066_, v___x_5114_);
                if v___x_5115_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5112_, 2);
                    crate::leanh::lean_dec(v_response_5109_);
                    crate::leanh::lean_dec(v_a_5061_);
                    crate::leanh::lean_dec_ref(v_kind_5050_);
                    crate::leanh::lean_dec_ref(v_params_5048_);
                    if v_isShared_5078_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5113_);
                        v___x_5117_ = v___x_5077_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5113_);
                        v___x_5117_ = v_reuseFailAlloc_5118_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5077_);
                    v___x_5119_ =
                        l_Array_toSubarray___redArg(v_response_5109_, v___x_5066_, v___x_5114_);
                    v___x_5120_ = crate::leanh::lean_box((v___x_5067_) as usize);
                    v___x_5121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5121_, 0, v___x_5120_);
                    crate::leanh::lean_ctor_set(v___x_5121_, 1, v___x_5119_);
                    v___x_5122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5122_, 0, v___x_5113_);
                    crate::leanh::lean_ctor_set(v___x_5122_, 1, v___x_5121_);
                    crate::leanh::lean_inc_ref(v_params_5048_);
                    crate::leanh::lean_inc_ref(v_doc_5053_);
                    v___x_5123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5050_, v_doc_5053_, v_params_5048_, v___x_5112_, v___x_5065_, v_a_5061_, v_sz_5069_, v___x_5070_, v___x_5122_, v_a_5051_);
                    crate::leanh::lean_dec(v_a_5061_);
                    if crate::leanh::lean_obj_tag(v___x_5123_) == 0 {
                        v_a_5124_ = crate::leanh::lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5142_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v___x_5126_ = v___x_5123_;
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5124_);
                            crate::leanh::lean_dec(v___x_5123_);
                            v___x_5126_ = crate::leanh::lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_params_5048_);
                        v_a_5143_ = crate::leanh::lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5150_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5123_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5143_);
                            crate::leanh::lean_dec(v___x_5123_);
                            v___x_5145_ = crate::leanh::lean_box(0);
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            11 => {
                return v___x_5117_;
            }
            12 => {
                v_snd_5128_ = crate::leanh::lean_ctor_get(v_a_5124_, 1);
                v_fst_5129_ = crate::leanh::lean_ctor_get(v_snd_5128_, 0);
                v___x_5130_ = (crate::leanh::lean_unbox(v_fst_5129_) as u8);
                if v___x_5130_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_5048_);
                    v_fst_5131_ = crate::leanh::lean_ctor_get(v_a_5124_, 0);
                    crate::leanh::lean_inc(v_fst_5131_);
                    crate::leanh::lean_dec(v_a_5124_);
                    if v_isShared_5127_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5126_, 0, v_fst_5131_);
                        v___x_5133_ = v___x_5126_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_fst_5131_);
                        v___x_5133_ = v_reuseFailAlloc_5134_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_fst_5135_ = crate::leanh::lean_ctor_get(v_a_5124_, 0);
                    crate::leanh::lean_inc(v_fst_5135_);
                    crate::leanh::lean_dec(v_a_5124_);
                    v___x_5136_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4;
                    v___x_5137_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
                        v_params_5048_,
                        v___x_5136_,
                    );
                    v___x_5138_ = lean_array_push(v_fst_5135_, v___x_5137_);
                    if v_isShared_5127_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5126_, 0, v___x_5138_);
                        v___x_5140_ = v___x_5126_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
                        v___x_5140_ = v_reuseFailAlloc_5141_;
                        state = 14;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_5133_;
            }
            14 => {
                return v___x_5140_;
            }
            15 => {
                if v_isShared_5146_ == 0 {
                    v___x_5148_ = v___x_5145_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5148_;
            }
            17 => {
                v___x_5163_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5164_ = lean_nat_add(v_line_5159_, v___x_5163_);
                crate::leanh::lean_dec(v_line_5159_);
                if v_isShared_5162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5161_, 1, v___x_5066_);
                    crate::leanh::lean_ctor_set(v___x_5161_, 0, v___x_5164_);
                    v___x_5166_ = v___x_5161_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5066_);
                    v___x_5166_ = v_reuseFailAlloc_5167_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_5111_ = v___x_5166_;
                state = 10;
                continue;
            }
            19 => {
                return v___x_5174_;
            }
            20 => {
                if v_isShared_5180_ == 0 {
                    v___x_5182_ = v___x_5179_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
                    v___x_5182_ = v_reuseFailAlloc_5183_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(
    mut v_id_5187_: *mut crate::leanh::LeanObject,
    mut v_params_5188_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_5189_: *mut crate::leanh::LeanObject,
    mut v_kind_5190_: *mut crate::leanh::LeanObject,
    mut v_a_5191_: *mut crate::leanh::LeanObject,
    mut v_a_5192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
        v_id_5187_,
        v_params_5188_,
        v_requestedRange_5189_,
        v_kind_5190_,
        v_a_5191_,
    );
    crate::leanh::lean_dec_ref(v_a_5191_);
    return v_res_5193_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(
    mut v_a_5194_: *mut crate::leanh::LeanObject,
    mut v_kind_5195_: *mut crate::leanh::LeanObject,
    mut v___x_5196_: *mut crate::leanh::LeanObject,
    mut v_params_5197_: *mut crate::leanh::LeanObject,
    mut v___x_5198_: *mut crate::leanh::LeanObject,
    mut v___x_5199_: *mut crate::leanh::LeanObject,
    mut v_as_5200_: *mut crate::leanh::LeanObject,
    mut v_sz_5201_: usize,
    mut v_i_5202_: usize,
    mut v_b_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_5194_, v_kind_5195_, v___x_5196_, v_params_5197_, v___x_5198_, v___x_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_);
    return v___x_5206_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(
    mut v_a_5207_: *mut crate::leanh::LeanObject,
    mut v_kind_5208_: *mut crate::leanh::LeanObject,
    mut v___x_5209_: *mut crate::leanh::LeanObject,
    mut v_params_5210_: *mut crate::leanh::LeanObject,
    mut v___x_5211_: *mut crate::leanh::LeanObject,
    mut v___x_5212_: *mut crate::leanh::LeanObject,
    mut v_as_5213_: *mut crate::leanh::LeanObject,
    mut v_sz_5214_: *mut crate::leanh::LeanObject,
    mut v_i_5215_: *mut crate::leanh::LeanObject,
    mut v_b_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5219_: usize = 0;
    let mut v_i_boxed_5220_: usize = 0;
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5219_ = crate::leanh::lean_unbox_usize(v_sz_5214_);
    crate::leanh::lean_dec(v_sz_5214_);
    v_i_boxed_5220_ = crate::leanh::lean_unbox_usize(v_i_5215_);
    crate::leanh::lean_dec(v_i_5215_);
    v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_5207_, v_kind_5208_, v___x_5209_, v_params_5210_, v___x_5211_, v___x_5212_, v_as_5213_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5216_, v___y_5217_);
    crate::leanh::lean_dec_ref(v___y_5217_);
    crate::leanh::lean_dec_ref(v_as_5213_);
    crate::leanh::lean_dec(v___x_5212_);
    return v_res_5221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_as_5226_: *mut crate::leanh::LeanObject,
    mut v_sz_5227_: usize,
    mut v_i_5228_: usize,
    mut v_b_5229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: usize = 0;
    let mut v___x_5235_: u8 = 0;
    let mut v_a_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_5238_: u8 = 0;
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
                if v___x_5235_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5225_);
                    crate::leanh::lean_inc_ref(v_b_5229_);
                    return v_b_5229_;
                } else {
                    v_a_5236_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
                    v_decl_5237_ = crate::leanh::lean_ctor_get(v_a_5236_, 1);
                    v_isExactMatch_5238_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5236_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_5239_ = crate::leanh::lean_box(0);
                    v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                    if v_isExactMatch_5238_ == 0 {
                        v_a_5231_ = v___x_5240_;
                        state = 1;
                        continue;
                    } else {
                        v_ctx_5241_ = crate::leanh::lean_ctor_get(v_a_5225_, 1);
                        v_toCommandContextInfo_5242_ = crate::leanh::lean_ctor_get(v_ctx_5241_, 0);
                        v_env_5243_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_5242_, 0);
                        crate::leanh::lean_inc(v_decl_5237_);
                        crate::leanh::lean_inc_ref(v_env_5243_);
                        v___x_5244_ = l_Lean_Environment_contains(
                            v_env_5243_,
                            v_decl_5237_,
                            v_isExactMatch_5238_,
                        );
                        if v___x_5244_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_5225_);
                            crate::leanh::lean_inc(v_a_5236_);
                            v___x_5245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5245_, 0, v_a_5236_);
                            v___x_5246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5246_, 0, v___x_5245_);
                            v___x_5247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                            crate::leanh::lean_ctor_set(v___x_5247_, 1, v___x_5239_);
                            return v___x_5247_;
                        } else {
                            v_a_5231_ = v___x_5240_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5232_ = 1usize;
                v___x_5233_ = lean_usize_add(v_i_5228_, v___x_5232_);
                v_i_5228_ = v___x_5233_;
                v_b_5229_ = v_a_5231_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(
    mut v_a_5248_: *mut crate::leanh::LeanObject,
    mut v_as_5249_: *mut crate::leanh::LeanObject,
    mut v_sz_5250_: *mut crate::leanh::LeanObject,
    mut v_i_5251_: *mut crate::leanh::LeanObject,
    mut v_b_5252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5253_: usize = 0;
    let mut v_i_boxed_5254_: usize = 0;
    let mut v_res_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5253_ = crate::leanh::lean_unbox_usize(v_sz_5250_);
    crate::leanh::lean_dec(v_sz_5250_);
    v_i_boxed_5254_ = crate::leanh::lean_unbox_usize(v_i_5251_);
    crate::leanh::lean_dec(v_i_5251_);
    v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5248_, v_as_5249_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5252_);
    crate::leanh::lean_dec_ref(v_b_5252_);
    crate::leanh::lean_dec_ref(v_as_5249_);
    return v_res_5255_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(
    mut v_a_5256_: *mut crate::leanh::LeanObject,
    mut v_x_5257_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5258_: u8 = 0;
    let mut v_key_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5257_) == 0 {
                    v___x_5258_ = 0;
                    return v___x_5258_;
                } else {
                    v_key_5259_ = crate::leanh::lean_ctor_get(v_x_5257_, 0);
                    v_tail_5260_ = crate::leanh::lean_ctor_get(v_x_5257_, 2);
                    v___x_5261_ = lean_name_eq(v_key_5259_, v_a_5256_);
                    if v___x_5261_ == 0 {
                        v_x_5257_ = v_tail_5260_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5261_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(
    mut v_a_5263_: *mut crate::leanh::LeanObject,
    mut v_x_5264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5265_: u8 = 0;
    let mut v_r_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5263_, v_x_5264_);
    crate::leanh::lean_dec(v_x_5264_);
    crate::leanh::lean_dec(v_a_5263_);
    v_r_5266_ = crate::leanh::lean_box((v_res_5265_) as usize);
    return v_r_5266_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u64 = 0;
    v___x_5267_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_5268_ = lean_uint64_of_nat(v___x_5267_);
    return v___x_5268_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(
    mut v_m_5269_: *mut crate::leanh::LeanObject,
    mut v_a_5270_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: u64 = 0;
    let mut v___x_5275_: u64 = 0;
    let mut v___x_5276_: u64 = 0;
    let mut v_fold_5277_: u64 = 0;
    let mut v___x_5278_: u64 = 0;
    let mut v___x_5279_: u64 = 0;
    let mut v___x_5280_: u64 = 0;
    let mut v___x_5281_: usize = 0;
    let mut v___x_5282_: usize = 0;
    let mut v___x_5283_: usize = 0;
    let mut v___x_5284_: usize = 0;
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: u64 = 0;
    let mut v_hash_5289_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5271_ = crate::leanh::lean_ctor_get(v_m_5269_, 1);
                v___x_5272_ = lean_array_get_size(v_buckets_5271_);
                if crate::leanh::lean_obj_tag(v_a_5270_) == 0 {
                    v___x_5288_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5274_ = v___x_5288_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5289_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5270_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5274_ = v_hash_5289_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5275_ = 32u64;
                v___x_5276_ = lean_uint64_shift_right(v___y_5274_, v___x_5275_);
                v_fold_5277_ = lean_uint64_xor(v___y_5274_, v___x_5276_);
                v___x_5278_ = 16u64;
                v___x_5279_ = lean_uint64_shift_right(v_fold_5277_, v___x_5278_);
                v___x_5280_ = lean_uint64_xor(v_fold_5277_, v___x_5279_);
                v___x_5281_ = lean_uint64_to_usize(v___x_5280_);
                v___x_5282_ = lean_usize_of_nat(v___x_5272_);
                v___x_5283_ = 1usize;
                v___x_5284_ = lean_usize_sub(v___x_5282_, v___x_5283_);
                v___x_5285_ = lean_usize_land(v___x_5281_, v___x_5284_);
                v___x_5286_ = lean_array_uget_borrowed(v_buckets_5271_, v___x_5285_);
                v___x_5287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5270_, v___x_5286_);
                return v___x_5287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___boxed(
    mut v_m_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5292_: u8 = 0;
    let mut v_r_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5290_, v_a_5291_);
    crate::leanh::lean_dec(v_a_5291_);
    crate::leanh::lean_dec_ref(v_m_5290_);
    v_r_5293_ = crate::leanh::lean_box((v_res_5292_) as usize);
    return v_r_5293_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(
    mut v_x_5294_: *mut crate::leanh::LeanObject,
    mut v_x_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5304_: u64 = 0;
    let mut v___x_5305_: u64 = 0;
    let mut v___x_5306_: u64 = 0;
    let mut v_fold_5307_: u64 = 0;
    let mut v___x_5308_: u64 = 0;
    let mut v___x_5309_: u64 = 0;
    let mut v___x_5310_: u64 = 0;
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: usize = 0;
    let mut v___x_5313_: usize = 0;
    let mut v___x_5314_: usize = 0;
    let mut v___x_5315_: usize = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u64 = 0;
    let mut v_hash_5323_: u64 = 0;
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5295_) == 0 {
                    return v_x_5294_;
                } else {
                    v_key_5296_ = crate::leanh::lean_ctor_get(v_x_5295_, 0);
                    v_value_5297_ = crate::leanh::lean_ctor_get(v_x_5295_, 1);
                    v_tail_5298_ = crate::leanh::lean_ctor_get(v_x_5295_, 2);
                    v_isSharedCheck_5324_ = (!crate::leanh::lean_is_exclusive(v_x_5295_)) as u8;
                    if v_isSharedCheck_5324_ == 0 {
                        v___x_5300_ = v_x_5295_;
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5298_);
                        crate::leanh::lean_inc(v_value_5297_);
                        crate::leanh::lean_inc(v_key_5296_);
                        crate::leanh::lean_dec(v_x_5295_);
                        v___x_5300_ = crate::leanh::lean_box(0);
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5302_ = lean_array_get_size(v_x_5294_);
                if crate::leanh::lean_obj_tag(v_key_5296_) == 0 {
                    v___x_5322_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5304_ = v___x_5322_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5323_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_5296_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5304_ = v_hash_5323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5305_ = 32u64;
                v___x_5306_ = lean_uint64_shift_right(v___y_5304_, v___x_5305_);
                v_fold_5307_ = lean_uint64_xor(v___y_5304_, v___x_5306_);
                v___x_5308_ = 16u64;
                v___x_5309_ = lean_uint64_shift_right(v_fold_5307_, v___x_5308_);
                v___x_5310_ = lean_uint64_xor(v_fold_5307_, v___x_5309_);
                v___x_5311_ = lean_uint64_to_usize(v___x_5310_);
                v___x_5312_ = lean_usize_of_nat(v___x_5302_);
                v___x_5313_ = 1usize;
                v___x_5314_ = lean_usize_sub(v___x_5312_, v___x_5313_);
                v___x_5315_ = lean_usize_land(v___x_5311_, v___x_5314_);
                v___x_5316_ = lean_array_uget_borrowed(v_x_5294_, v___x_5315_);
                crate::leanh::lean_inc(v___x_5316_);
                if v_isShared_5301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5300_, 2, v___x_5316_);
                    v___x_5318_ = v___x_5300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_key_5296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_value_5297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 2, v___x_5316_);
                    v___x_5318_ = v_reuseFailAlloc_5321_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5319_ = lean_array_uset(v_x_5294_, v___x_5315_, v___x_5318_);
                v_x_5294_ = v___x_5319_;
                v_x_5295_ = v_tail_5298_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(
    mut v_i_5325_: *mut crate::leanh::LeanObject,
    mut v_source_5326_: *mut crate::leanh::LeanObject,
    mut v_target_5327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: u8 = 0;
    let mut v_es_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5328_ = lean_array_get_size(v_source_5326_);
                v___x_5329_ = lean_nat_dec_lt(v_i_5325_, v___x_5328_);
                if v___x_5329_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5326_);
                    crate::leanh::lean_dec(v_i_5325_);
                    return v_target_5327_;
                } else {
                    v_es_5330_ = lean_array_fget(v_source_5326_, v_i_5325_);
                    v___x_5331_ = crate::leanh::lean_box(0);
                    v_source_5332_ = lean_array_fset(v_source_5326_, v_i_5325_, v___x_5331_);
                    v_target_5333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_5327_, v_es_5330_);
                    v___x_5334_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5335_ = lean_nat_add(v_i_5325_, v___x_5334_);
                    crate::leanh::lean_dec(v_i_5325_);
                    v_i_5325_ = v___x_5335_;
                    v_source_5326_ = v_source_5332_;
                    v_target_5327_ = v_target_5333_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(
    mut v_data_5337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5338_ = lean_array_get_size(v_data_5337_);
    v___x_5339_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5340_ = lean_nat_mul(v___x_5338_, v___x_5339_);
    v___x_5341_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5342_ = crate::leanh::lean_box(0);
    v___x_5343_ = lean_mk_array(v_nbuckets_5340_, v___x_5342_);
    v___x_5344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_5341_, v_data_5337_, v___x_5343_);
    return v___x_5344_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(
    mut v_m_5345_: *mut crate::leanh::LeanObject,
    mut v_a_5346_: *mut crate::leanh::LeanObject,
    mut v_b_5347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5352_: u64 = 0;
    let mut v___x_5353_: u64 = 0;
    let mut v___x_5354_: u64 = 0;
    let mut v_fold_5355_: u64 = 0;
    let mut v___x_5356_: u64 = 0;
    let mut v___x_5357_: u64 = 0;
    let mut v___x_5358_: u64 = 0;
    let mut v___x_5359_: usize = 0;
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: usize = 0;
    let mut v___x_5363_: usize = 0;
    let mut v_bkt_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v_val_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_unused_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: u64 = 0;
    let mut v_hash_5390_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5348_ = crate::leanh::lean_ctor_get(v_m_5345_, 0);
                v_buckets_5349_ = crate::leanh::lean_ctor_get(v_m_5345_, 1);
                v___x_5350_ = lean_array_get_size(v_buckets_5349_);
                if crate::leanh::lean_obj_tag(v_a_5346_) == 0 {
                    v___x_5389_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5352_ = v___x_5389_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5390_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5346_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5352_ = v_hash_5390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5353_ = 32u64;
                v___x_5354_ = lean_uint64_shift_right(v___y_5352_, v___x_5353_);
                v_fold_5355_ = lean_uint64_xor(v___y_5352_, v___x_5354_);
                v___x_5356_ = 16u64;
                v___x_5357_ = lean_uint64_shift_right(v_fold_5355_, v___x_5356_);
                v___x_5358_ = lean_uint64_xor(v_fold_5355_, v___x_5357_);
                v___x_5359_ = lean_uint64_to_usize(v___x_5358_);
                v___x_5360_ = lean_usize_of_nat(v___x_5350_);
                v___x_5361_ = 1usize;
                v___x_5362_ = lean_usize_sub(v___x_5360_, v___x_5361_);
                v___x_5363_ = lean_usize_land(v___x_5359_, v___x_5362_);
                v_bkt_5364_ = lean_array_uget_borrowed(v_buckets_5349_, v___x_5363_);
                v___x_5365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5346_, v_bkt_5364_);
                if v___x_5365_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_5349_);
                    crate::leanh::lean_inc(v_size_5348_);
                    v_isSharedCheck_5386_ = (!crate::leanh::lean_is_exclusive(v_m_5345_)) as u8;
                    if v_isSharedCheck_5386_ == 0 {
                        v_unused_5387_ = crate::leanh::lean_ctor_get(v_m_5345_, 1);
                        crate::leanh::lean_dec(v_unused_5387_);
                        v_unused_5388_ = crate::leanh::lean_ctor_get(v_m_5345_, 0);
                        crate::leanh::lean_dec(v_unused_5388_);
                        v___x_5367_ = v_m_5345_;
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5345_);
                        v___x_5367_ = crate::leanh::lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5347_);
                    crate::leanh::lean_dec(v_a_5346_);
                    return v_m_5345_;
                }
            }
            2 => {
                v___x_5369_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5370_ = lean_nat_add(v_size_5348_, v___x_5369_);
                crate::leanh::lean_dec(v_size_5348_);
                crate::leanh::lean_inc(v_bkt_5364_);
                v___x_5371_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5371_, 0, v_a_5346_);
                crate::leanh::lean_ctor_set(v___x_5371_, 1, v_b_5347_);
                crate::leanh::lean_ctor_set(v___x_5371_, 2, v_bkt_5364_);
                v_buckets_x27_5372_ = lean_array_uset(v_buckets_5349_, v___x_5363_, v___x_5371_);
                v___x_5373_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5374_ = lean_nat_mul(v_size_x27_5370_, v___x_5373_);
                v___x_5375_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5376_ = lean_nat_div(v___x_5374_, v___x_5375_);
                crate::leanh::lean_dec(v___x_5374_);
                v___x_5377_ = lean_array_get_size(v_buckets_x27_5372_);
                v___x_5378_ = lean_nat_dec_le(v___x_5376_, v___x_5377_);
                crate::leanh::lean_dec(v___x_5376_);
                if v___x_5378_ == 0 {
                    v_val_5379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_5372_);
                    if v_isShared_5368_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5367_, 1, v_val_5379_);
                        crate::leanh::lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5381_ = v___x_5367_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_size_x27_5370_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_val_5379_);
                        v___x_5381_ = v_reuseFailAlloc_5382_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_5368_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5367_, 1, v_buckets_x27_5372_);
                        crate::leanh::lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5384_ = v___x_5367_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_size_x27_5370_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 1, v_buckets_x27_5372_);
                        v___x_5384_ = v_reuseFailAlloc_5385_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5381_;
            }
            4 => {
                return v___x_5384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(
    mut v___x_5391_: *mut crate::leanh::LeanObject,
    mut v_as_5392_: *mut crate::leanh::LeanObject,
    mut v_sz_5393_: usize,
    mut v_i_5394_: usize,
    mut v_b_5395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: usize = 0;
    let mut v___x_5400_: usize = 0;
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v_fst_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v_array_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v_a_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5433_: usize = 0;
    let mut v___x_5434_: usize = 0;
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edits_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_unused_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5488_: u8 = 0;
    let mut v_unused_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5490_: u8 = 0;
    let mut v_unused_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_unused_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5496_: u8 = 0;
    let mut v_unused_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5402_ = lean_usize_dec_lt(v_i_5394_, v_sz_5393_);
                if v___x_5402_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5391_);
                    v___x_5403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5403_, 0, v_b_5395_);
                    return v___x_5403_;
                } else {
                    v_snd_5404_ = crate::leanh::lean_ctor_get(v_b_5395_, 1);
                    crate::leanh::lean_inc(v_snd_5404_);
                    v_snd_5405_ = crate::leanh::lean_ctor_get(v_snd_5404_, 1);
                    crate::leanh::lean_inc(v_snd_5405_);
                    v_fst_5406_ = crate::leanh::lean_ctor_get(v_b_5395_, 0);
                    v_isSharedCheck_5496_ = (!crate::leanh::lean_is_exclusive(v_b_5395_)) as u8;
                    if v_isSharedCheck_5496_ == 0 {
                        v_unused_5497_ = crate::leanh::lean_ctor_get(v_b_5395_, 1);
                        crate::leanh::lean_dec(v_unused_5497_);
                        v___x_5408_ = v_b_5395_;
                        v_isShared_5409_ = v_isSharedCheck_5496_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_5406_);
                        crate::leanh::lean_dec(v_b_5395_);
                        v___x_5408_ = crate::leanh::lean_box(0);
                        v_isShared_5409_ = v_isSharedCheck_5496_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5399_ = 1usize;
                v___x_5400_ = lean_usize_add(v_i_5394_, v___x_5399_);
                v_i_5394_ = v___x_5400_;
                v_b_5395_ = v_a_5398_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_5410_ = crate::leanh::lean_ctor_get(v_snd_5404_, 0);
                v_isSharedCheck_5494_ = (!crate::leanh::lean_is_exclusive(v_snd_5404_)) as u8;
                if v_isSharedCheck_5494_ == 0 {
                    v_unused_5495_ = crate::leanh::lean_ctor_get(v_snd_5404_, 1);
                    crate::leanh::lean_dec(v_unused_5495_);
                    v___x_5412_ = v_snd_5404_;
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5410_);
                    crate::leanh::lean_dec(v_snd_5404_);
                    v___x_5412_ = crate::leanh::lean_box(0);
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_5414_ = crate::leanh::lean_ctor_get(v_snd_5405_, 0);
                v_start_5415_ = crate::leanh::lean_ctor_get(v_snd_5405_, 1);
                v_stop_5416_ = crate::leanh::lean_ctor_get(v_snd_5405_, 2);
                v___x_5417_ = lean_nat_dec_lt(v_start_5415_, v_stop_5416_);
                if v___x_5417_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5391_);
                    if v_isShared_5413_ == 0 {
                        v___x_5419_ = v___x_5412_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_fst_5410_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_snd_5405_);
                        v___x_5419_ = v_reuseFailAlloc_5424_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_5416_);
                    crate::leanh::lean_inc(v_start_5415_);
                    crate::leanh::lean_inc_ref(v_array_5414_);
                    v_isSharedCheck_5490_ = (!crate::leanh::lean_is_exclusive(v_snd_5405_)) as u8;
                    if v_isSharedCheck_5490_ == 0 {
                        v_unused_5491_ = crate::leanh::lean_ctor_get(v_snd_5405_, 2);
                        crate::leanh::lean_dec(v_unused_5491_);
                        v_unused_5492_ = crate::leanh::lean_ctor_get(v_snd_5405_, 1);
                        crate::leanh::lean_dec(v_unused_5492_);
                        v_unused_5493_ = crate::leanh::lean_ctor_get(v_snd_5405_, 0);
                        crate::leanh::lean_dec(v_unused_5493_);
                        v___x_5426_ = v_snd_5405_;
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_5405_);
                        v___x_5426_ = crate::leanh::lean_box(0);
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5408_, 1, v___x_5419_);
                    v___x_5421_ = v___x_5408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_fst_5406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5419_);
                    v___x_5421_ = v_reuseFailAlloc_5423_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5422_, 0, v___x_5421_);
                return v___x_5422_;
            }
            6 => {
                v_a_5428_ = lean_array_uget_borrowed(v_as_5392_, v_i_5394_);
                v___x_5429_ = lean_array_fget_borrowed(v_array_5414_, v_start_5415_);
                v___x_5430_ = crate::leanh::lean_box(0);
                v___x_5431_ = crate::leanh::lean_box(0);
                v___x_5432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                v_sz_5433_ = lean_array_size(v___x_5429_);
                v___x_5434_ = 0usize;
                crate::leanh::lean_inc(v_a_5428_);
                v___x_5435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5428_, v___x_5429_, v_sz_5433_, v___x_5434_, v___x_5432_);
                v_fst_5436_ = crate::leanh::lean_ctor_get(v___x_5435_, 0);
                v_isSharedCheck_5488_ = (!crate::leanh::lean_is_exclusive(v___x_5435_)) as u8;
                if v_isSharedCheck_5488_ == 0 {
                    v_unused_5489_ = crate::leanh::lean_ctor_get(v___x_5435_, 1);
                    crate::leanh::lean_dec(v_unused_5489_);
                    v___x_5438_ = v___x_5435_;
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5436_);
                    crate::leanh::lean_dec(v___x_5435_);
                    v___x_5438_ = crate::leanh::lean_box(0);
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5440_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5441_ = lean_nat_add(v_start_5415_, v___x_5440_);
                crate::leanh::lean_dec(v_start_5415_);
                if v_isShared_5427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5426_, 1, v___x_5441_);
                    v___x_5443_ = v___x_5426_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5487_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_array_5414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_stop_5416_);
                    v___x_5443_ = v_reuseFailAlloc_5487_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_fst_5436_) == 0 {
                    crate::leanh::lean_del_object(v___x_5408_);
                    state = 9;
                    continue;
                } else {
                    v_val_5451_ = crate::leanh::lean_ctor_get(v_fst_5436_, 0);
                    crate::leanh::lean_inc(v_val_5451_);
                    crate::leanh::lean_dec_ref_known(v_fst_5436_, 1);
                    if crate::leanh::lean_obj_tag(v_val_5451_) == 1 {
                        crate::leanh::lean_del_object(v___x_5438_);
                        crate::leanh::lean_del_object(v___x_5412_);
                        v_val_5452_ = crate::leanh::lean_ctor_get(v_val_5451_, 0);
                        crate::leanh::lean_inc(v_val_5452_);
                        crate::leanh::lean_dec_ref_known(v_val_5451_, 1);
                        v_ctx_5453_ = crate::leanh::lean_ctor_get(v_a_5428_, 1);
                        v_toCommandContextInfo_5454_ = crate::leanh::lean_ctor_get(v_ctx_5453_, 0);
                        v_module_5455_ = crate::leanh::lean_ctor_get(v_val_5452_, 0);
                        crate::leanh::lean_inc(v_module_5455_);
                        v_decl_5456_ = crate::leanh::lean_ctor_get(v_val_5452_, 1);
                        crate::leanh::lean_inc(v_decl_5456_);
                        crate::leanh::lean_dec(v_val_5452_);
                        v_determineInsertion_5457_ = crate::leanh::lean_ctor_get(v_a_5428_, 2);
                        v_env_5458_ = crate::leanh::lean_ctor_get(v_toCommandContextInfo_5454_, 0);
                        v___x_5459_ = l_Lean_Environment_mainModule(v_env_5458_);
                        v___x_5460_ = lean_name_eq(v_module_5455_, v___x_5459_);
                        crate::leanh::lean_dec(v___x_5459_);
                        if v___x_5460_ == 0 {
                            crate::leanh::lean_inc_ref(v_determineInsertion_5457_);
                            v___x_5461_ = crate::leanh::lean_apply_1(
                                v_determineInsertion_5457_,
                                v_decl_5456_,
                            );
                            v___x_5482_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_fst_5410_, v_module_5455_);
                            if v___x_5482_ == 0 {
                                state = 16;
                                continue;
                            } else {
                                if v___x_5460_ == 0 {
                                    v_edits_5463_ = v_fst_5406_;
                                    state = 12;
                                    continue;
                                } else {
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_decl_5456_);
                            crate::leanh::lean_dec(v_module_5455_);
                            if v_isShared_5409_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                                crate::leanh::lean_ctor_set(v___x_5408_, 0, v_fst_5410_);
                                v___x_5484_ = v___x_5408_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_5486_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_fst_5410_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5486_, 1, v___x_5443_);
                                v___x_5484_ = v_reuseFailAlloc_5486_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5451_);
                        crate::leanh::lean_del_object(v___x_5408_);
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5438_, 1, v___x_5443_);
                    crate::leanh::lean_ctor_set(v___x_5438_, 0, v_fst_5410_);
                    v___x_5446_ = v___x_5438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_fst_5410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 1, v___x_5443_);
                    v___x_5446_ = v_reuseFailAlloc_5450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5412_, 1, v___x_5446_);
                    crate::leanh::lean_ctor_set(v___x_5412_, 0, v_fst_5406_);
                    v___x_5448_ = v___x_5412_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5446_);
                    v___x_5448_ = v_reuseFailAlloc_5449_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_5398_ = v___x_5448_;
                state = 1;
                continue;
            }
            12 => {
                v_edit_5464_ = crate::leanh::lean_ctor_get(v___x_5461_, 1);
                v_isSharedCheck_5476_ = (!crate::leanh::lean_is_exclusive(v___x_5461_)) as u8;
                if v_isSharedCheck_5476_ == 0 {
                    v_unused_5477_ = crate::leanh::lean_ctor_get(v___x_5461_, 0);
                    crate::leanh::lean_dec(v_unused_5477_);
                    v___x_5466_ = v___x_5461_;
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_edit_5464_);
                    crate::leanh::lean_dec(v___x_5461_);
                    v___x_5466_ = crate::leanh::lean_box(0);
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5468_ = lean_array_push(v_edits_5463_, v_edit_5464_);
                v___x_5469_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_5410_, v_module_5455_, v___x_5431_);
                if v_isShared_5409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                    crate::leanh::lean_ctor_set(v___x_5408_, 0, v___x_5469_);
                    v___x_5471_ = v___x_5408_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 1, v___x_5443_);
                    v___x_5471_ = v_reuseFailAlloc_5475_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5466_, 1, v___x_5471_);
                    crate::leanh::lean_ctor_set(v___x_5466_, 0, v___x_5468_);
                    v___x_5473_ = v___x_5466_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5471_);
                    v___x_5473_ = v_reuseFailAlloc_5474_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_a_5398_ = v___x_5473_;
                state = 1;
                continue;
            }
            16 => {
                crate::leanh::lean_inc(v_module_5455_);
                crate::leanh::lean_inc_ref(v_ctx_5453_);
                v___x_5479_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_5453_, v_module_5455_);
                crate::leanh::lean_inc_ref(v___x_5391_);
                v___x_5480_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5480_, 0, v___x_5391_);
                crate::leanh::lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                crate::leanh::lean_ctor_set(v___x_5480_, 2, v___x_5430_);
                crate::leanh::lean_ctor_set(v___x_5480_, 3, v___x_5430_);
                v___x_5481_ = lean_array_push(v_fst_5406_, v___x_5480_);
                v_edits_5463_ = v___x_5481_;
                state = 12;
                continue;
            }
            17 => {
                v___x_5485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5485_, 0, v_fst_5406_);
                crate::leanh::lean_ctor_set(v___x_5485_, 1, v___x_5484_);
                v_a_5398_ = v___x_5485_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(
    mut v___x_5498_: *mut crate::leanh::LeanObject,
    mut v_as_5499_: *mut crate::leanh::LeanObject,
    mut v_sz_5500_: *mut crate::leanh::LeanObject,
    mut v_i_5501_: *mut crate::leanh::LeanObject,
    mut v_b_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5504_: usize = 0;
    let mut v_i_boxed_5505_: usize = 0;
    let mut v_res_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5504_ = crate::leanh::lean_unbox_usize(v_sz_5500_);
    crate::leanh::lean_dec(v_sz_5500_);
    v_i_boxed_5505_ = crate::leanh::lean_unbox_usize(v_i_5501_);
    crate::leanh::lean_dec(v_i_5501_);
    v_res_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5498_, v_as_5499_, v_sz_boxed_5504_, v_i_boxed_5505_, v_b_5502_);
    crate::leanh::lean_dec_ref(v_as_5499_);
    return v_res_5506_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(
    mut v___x_5507_: *mut crate::leanh::LeanObject,
    mut v_as_5508_: *mut crate::leanh::LeanObject,
    mut v_i_5509_: usize,
    mut v_stop_5510_: usize,
    mut v_b_5511_: *mut crate::leanh::LeanObject,
    mut v___y_5512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: usize = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5519_ = lean_usize_dec_eq(v_i_5509_, v_stop_5510_);
                if v___x_5519_ == 0 {
                    v___x_5520_ = lean_array_uget_borrowed(v_as_5508_, v_i_5509_);
                    v_stop_5521_ = crate::leanh::lean_ctor_get(v___x_5520_, 1);
                    crate::leanh::lean_inc(v_stop_5521_);
                    crate::leanh::lean_inc_ref(v___x_5507_);
                    v___x_5522_ = l_Lean_Server_FileWorker_computeQueries(
                        v___x_5507_,
                        v_stop_5521_,
                        v___y_5512_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5522_) == 0 {
                        v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5522_, 0);
                        crate::leanh::lean_inc(v_a_5523_);
                        crate::leanh::lean_dec_ref_known(v___x_5522_, 1);
                        v___x_5524_ = l_Array_append___redArg(v_b_5511_, v_a_5523_);
                        crate::leanh::lean_dec(v_a_5523_);
                        v_a_5515_ = v___x_5524_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5511_);
                        if crate::leanh::lean_obj_tag(v___x_5522_) == 0 {
                            v_a_5525_ = crate::leanh::lean_ctor_get(v___x_5522_, 0);
                            crate::leanh::lean_inc(v_a_5525_);
                            crate::leanh::lean_dec_ref_known(v___x_5522_, 1);
                            v_a_5515_ = v_a_5525_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5507_);
                            return v___x_5522_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5507_);
                    v___x_5526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5526_, 0, v_b_5511_);
                    return v___x_5526_;
                }
            }
            1 => {
                v___x_5516_ = 1usize;
                v___x_5517_ = lean_usize_add(v_i_5509_, v___x_5516_);
                v_i_5509_ = v___x_5517_;
                v_b_5511_ = v_a_5515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4___boxed(
    mut v___x_5527_: *mut crate::leanh::LeanObject,
    mut v_as_5528_: *mut crate::leanh::LeanObject,
    mut v_i_5529_: *mut crate::leanh::LeanObject,
    mut v_stop_5530_: *mut crate::leanh::LeanObject,
    mut v_b_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5534_: usize = 0;
    let mut v_stop_boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5534_ = crate::leanh::lean_unbox_usize(v_i_5529_);
    crate::leanh::lean_dec(v_i_5529_);
    v_stop_boxed_5535_ = crate::leanh::lean_unbox_usize(v_stop_5530_);
    crate::leanh::lean_dec(v_stop_5530_);
    v_res_5536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_5527_, v_as_5528_, v_i_boxed_5534_, v_stop_boxed_5535_, v_b_5531_, v___y_5532_);
    crate::leanh::lean_dec_ref(v___y_5532_);
    crate::leanh::lean_dec_ref(v_as_5528_);
    return v_res_5536_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5537_ = crate::leanh::lean_box(0);
    v___x_5538_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5539_ = lean_mk_array(v___x_5538_, v___x_5537_);
    return v___x_5539_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
    mut v_id_5542_: *mut crate::leanh::LeanObject,
    mut v_action_5543_: *mut crate::leanh::LeanObject,
    mut v_unknownIdentifierRanges_5544_: *mut crate::leanh::LeanObject,
    mut v_a_5545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: usize = 0;
    let mut v___y_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: usize = 0;
    let mut v___y_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v_fst_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v_toWorkDoneProgressParams_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_x3f_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreferred_x3f_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disabled_x3f_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_command_x3f_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_unused_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_unused_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_a_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut v_toEditableDocumentCore_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSnap_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5620_: usize = 0;
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut v_unused_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: u8 = 0;
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5547_ = crate::leanh::lean_ctor_get(v_a_5545_, 1);
                v_toEditableDocumentCore_5610_ = crate::leanh::lean_ctor_get(v_doc_5547_, 0);
                v_meta_5611_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5610_, 0);
                v_initSnap_5612_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5610_, 1);
                v_text_5613_ = crate::leanh::lean_ctor_get(v_meta_5611_, 3);
                v___x_5665_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5666_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1;
                v___x_5667_ = lean_array_get_size(v_unknownIdentifierRanges_5544_);
                v___x_5668_ = lean_nat_dec_lt(v___x_5665_, v___x_5667_);
                if v___x_5668_ == 0 {
                    v_a_5615_ = v___x_5666_;
                    state = 10;
                    continue;
                } else {
                    v___x_5669_ = lean_nat_dec_le(v___x_5667_, v___x_5667_);
                    if v___x_5669_ == 0 {
                        if v___x_5668_ == 0 {
                            v_a_5615_ = v___x_5666_;
                            state = 10;
                            continue;
                        } else {
                            v___x_5670_ = 0usize;
                            v___x_5671_ = lean_usize_of_nat(v___x_5667_);
                            crate::leanh::lean_inc_ref(v_doc_5547_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5670_, v___x_5671_, v___x_5666_, v_a_5545_);
                            v___y_5655_ = v___x_5672_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_5673_ = 0usize;
                        v___x_5674_ = lean_usize_of_nat(v___x_5667_);
                        crate::leanh::lean_inc_ref(v_doc_5547_);
                        v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5673_, v___x_5674_, v___x_5666_, v_a_5545_);
                        v___y_5655_ = v___x_5675_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_5554_);
                v___x_5555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5555_, 0, v___y_5554_);
                crate::leanh::lean_ctor_set(v___x_5555_, 1, v___y_5554_);
                v___x_5556_ = lean_mk_empty_array_with_capacity(v___y_5552_);
                v___x_5557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once), _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
                crate::leanh::lean_inc(v___y_5552_);
                v___x_5558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5558_, 0, v___y_5552_);
                crate::leanh::lean_ctor_set(v___x_5558_, 1, v___x_5557_);
                v___x_5559_ = lean_array_get_size(v___y_5553_);
                v___x_5560_ = l_Array_toSubarray___redArg(v___y_5553_, v___y_5552_, v___x_5559_);
                v___x_5561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5561_, 0, v___x_5558_);
                crate::leanh::lean_ctor_set(v___x_5561_, 1, v___x_5560_);
                v___x_5562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5562_, 0, v___x_5556_);
                crate::leanh::lean_ctor_set(v___x_5562_, 1, v___x_5561_);
                v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5555_, v___y_5550_, v___y_5549_, v___y_5551_, v___x_5562_);
                crate::leanh::lean_dec_ref(v___y_5550_);
                if crate::leanh::lean_obj_tag(v___x_5563_) == 0 {
                    v_a_5564_ = crate::leanh::lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5601_ = (!crate::leanh::lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5601_ == 0 {
                        v___x_5566_ = v___x_5563_;
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5564_);
                        crate::leanh::lean_dec(v___x_5563_);
                        v___x_5566_ = crate::leanh::lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_action_5543_);
                    v_a_5602_ = crate::leanh::lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5609_ = (!crate::leanh::lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v___x_5563_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5602_);
                        crate::leanh::lean_dec(v___x_5563_);
                        v___x_5604_ = crate::leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5568_ = crate::leanh::lean_ctor_get(v_a_5564_, 0);
                v_isSharedCheck_5599_ = (!crate::leanh::lean_is_exclusive(v_a_5564_)) as u8;
                if v_isSharedCheck_5599_ == 0 {
                    v_unused_5600_ = crate::leanh::lean_ctor_get(v_a_5564_, 1);
                    crate::leanh::lean_dec(v_unused_5600_);
                    v___x_5570_ = v_a_5564_;
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5568_);
                    crate::leanh::lean_dec(v_a_5564_);
                    v___x_5570_ = crate::leanh::lean_box(0);
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toWorkDoneProgressParams_5572_ = crate::leanh::lean_ctor_get(v_action_5543_, 0);
                v_toPartialResultParams_5573_ = crate::leanh::lean_ctor_get(v_action_5543_, 1);
                v_title_5574_ = crate::leanh::lean_ctor_get(v_action_5543_, 2);
                v_kind_x3f_5575_ = crate::leanh::lean_ctor_get(v_action_5543_, 3);
                v_diagnostics_x3f_5576_ = crate::leanh::lean_ctor_get(v_action_5543_, 4);
                v_isPreferred_x3f_5577_ = crate::leanh::lean_ctor_get(v_action_5543_, 5);
                v_disabled_x3f_5578_ = crate::leanh::lean_ctor_get(v_action_5543_, 6);
                v_command_x3f_5579_ = crate::leanh::lean_ctor_get(v_action_5543_, 8);
                v_data_x3f_5580_ = crate::leanh::lean_ctor_get(v_action_5543_, 9);
                v_isSharedCheck_5597_ = (!crate::leanh::lean_is_exclusive(v_action_5543_)) as u8;
                if v_isSharedCheck_5597_ == 0 {
                    v_unused_5598_ = crate::leanh::lean_ctor_get(v_action_5543_, 7);
                    crate::leanh::lean_dec(v_unused_5598_);
                    v___x_5582_ = v_action_5543_;
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_data_x3f_5580_);
                    crate::leanh::lean_inc(v_command_x3f_5579_);
                    crate::leanh::lean_inc(v_disabled_x3f_5578_);
                    crate::leanh::lean_inc(v_isPreferred_x3f_5577_);
                    crate::leanh::lean_inc(v_diagnostics_x3f_5576_);
                    crate::leanh::lean_inc(v_kind_x3f_5575_);
                    crate::leanh::lean_inc(v_title_5574_);
                    crate::leanh::lean_inc(v_toPartialResultParams_5573_);
                    crate::leanh::lean_inc(v_toWorkDoneProgressParams_5572_);
                    crate::leanh::lean_dec(v_action_5543_);
                    v___x_5582_ = crate::leanh::lean_box(0);
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_doc_5547_);
                v___x_5584_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_5547_);
                if v_isShared_5571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5570_, 1, v_fst_5568_);
                    crate::leanh::lean_ctor_set(v___x_5570_, 0, v___x_5584_);
                    v___x_5586_ = v___x_5570_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_fst_5568_);
                    v___x_5586_ = v_reuseFailAlloc_5596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5587_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_5586_);
                v___x_5588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5588_, 0, v___x_5587_);
                if v_isShared_5583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5582_, 7, v___x_5588_);
                    v___x_5590_ = v___x_5582_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5595_,
                        0,
                        v_toWorkDoneProgressParams_5572_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5595_,
                        1,
                        v_toPartialResultParams_5573_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_title_5574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 3, v_kind_x3f_5575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 4, v_diagnostics_x3f_5576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 5, v_isPreferred_x3f_5577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 6, v_disabled_x3f_5578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 7, v___x_5588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 8, v_command_x3f_5579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 9, v_data_x3f_5580_);
                    v___x_5590_ = v_reuseFailAlloc_5595_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5591_, 0, v___x_5590_);
                if v_isShared_5567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5566_, 0, v___x_5591_);
                    v___x_5593_ = v___x_5566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5591_);
                    v___x_5593_ = v_reuseFailAlloc_5594_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5593_;
            }
            8 => {
                if v_isShared_5605_ == 0 {
                    v___x_5607_ = v___x_5604_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
                    v___x_5607_ = v_reuseFailAlloc_5608_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5607_;
            }
            10 => {
                v___x_5616_ = lean_array_get_size(v_a_5615_);
                v___x_5617_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5618_ = lean_nat_dec_eq(v___x_5616_, v___x_5617_);
                if v___x_5618_ == 0 {
                    v___x_5619_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5620_ = lean_array_size(v_a_5615_);
                    v___x_5621_ = 0usize;
                    crate::leanh::lean_inc_ref(v_a_5615_);
                    v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5620_, v___x_5621_, v_a_5615_);
                    v___x_5623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5623_, 0, v_id_5542_);
                    crate::leanh::lean_ctor_set(v___x_5623_, 1, v___x_5622_);
                    v___x_5624_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5619_, v___x_5623_, v_a_5545_);
                    v_a_5625_ = crate::leanh::lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5651_ = (!crate::leanh::lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5651_ == 0 {
                        v___x_5627_ = v___x_5624_;
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5625_);
                        crate::leanh::lean_dec(v___x_5624_);
                        v___x_5627_ = crate::leanh::lean_box(0);
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5615_);
                    crate::leanh::lean_dec_ref(v_action_5543_);
                    crate::leanh::lean_dec(v_id_5542_);
                    v___x_5652_ = crate::leanh::lean_box(0);
                    v___x_5653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5653_, 0, v___x_5652_);
                    return v___x_5653_;
                }
            }
            11 => {
                v___x_5629_ = lean_task_get_own(v_a_5625_);
                if crate::leanh::lean_obj_tag(v___x_5629_) == 0 {
                    crate::leanh::lean_del_object(v___x_5627_);
                    v_response_5630_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                    crate::leanh::lean_inc(v_response_5630_);
                    crate::leanh::lean_dec_ref_known(v___x_5629_, 1);
                    v_stx_5631_ = crate::leanh::lean_ctor_get(v_initSnap_5612_, 3);
                    v___x_5632_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5631_, v___x_5618_);
                    if crate::leanh::lean_obj_tag(v___x_5632_) == 0 {
                        v___x_5633_ =
                            l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5;
                        v___y_5549_ = v_sz_5620_;
                        v___y_5550_ = v_a_5615_;
                        v___y_5551_ = v___x_5621_;
                        v___y_5552_ = v___x_5617_;
                        v___y_5553_ = v_response_5630_;
                        v___y_5554_ = v___x_5633_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5634_ = crate::leanh::lean_ctor_get(v___x_5632_, 0);
                        crate::leanh::lean_inc(v_val_5634_);
                        crate::leanh::lean_dec_ref_known(v___x_5632_, 1);
                        crate::leanh::lean_inc_ref(v_text_5613_);
                        v___x_5635_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5613_, v_val_5634_);
                        crate::leanh::lean_dec(v_val_5634_);
                        v_line_5636_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                        v_isSharedCheck_5645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5635_)) as u8;
                        if v_isSharedCheck_5645_ == 0 {
                            v_unused_5646_ = crate::leanh::lean_ctor_get(v___x_5635_, 1);
                            crate::leanh::lean_dec(v_unused_5646_);
                            v___x_5638_ = v___x_5635_;
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_line_5636_);
                            crate::leanh::lean_dec(v___x_5635_);
                            v___x_5638_ = crate::leanh::lean_box(0);
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5629_);
                    crate::leanh::lean_dec_ref(v_a_5615_);
                    crate::leanh::lean_dec_ref(v_action_5543_);
                    v___x_5647_ = crate::leanh::lean_box(0);
                    if v_isShared_5628_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5627_, 0, v___x_5647_);
                        v___x_5649_ = v___x_5627_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5647_);
                        v___x_5649_ = v_reuseFailAlloc_5650_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5640_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5641_ = lean_nat_add(v_line_5636_, v___x_5640_);
                crate::leanh::lean_dec(v_line_5636_);
                if v_isShared_5639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5638_, 1, v___x_5617_);
                    crate::leanh::lean_ctor_set(v___x_5638_, 0, v___x_5641_);
                    v___x_5643_ = v___x_5638_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 1, v___x_5617_);
                    v___x_5643_ = v_reuseFailAlloc_5644_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_5549_ = v_sz_5620_;
                v___y_5550_ = v_a_5615_;
                v___y_5551_ = v___x_5621_;
                v___y_5552_ = v___x_5617_;
                v___y_5553_ = v_response_5630_;
                v___y_5554_ = v___x_5643_;
                state = 1;
                continue;
            }
            14 => {
                return v___x_5649_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_5655_) == 0 {
                    v_a_5656_ = crate::leanh::lean_ctor_get(v___y_5655_, 0);
                    crate::leanh::lean_inc(v_a_5656_);
                    crate::leanh::lean_dec_ref_known(v___y_5655_, 1);
                    v_a_5615_ = v_a_5656_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_action_5543_);
                    crate::leanh::lean_dec(v_id_5542_);
                    v_a_5657_ = crate::leanh::lean_ctor_get(v___y_5655_, 0);
                    v_isSharedCheck_5664_ = (!crate::leanh::lean_is_exclusive(v___y_5655_)) as u8;
                    if v_isSharedCheck_5664_ == 0 {
                        v___x_5659_ = v___y_5655_;
                        v_isShared_5660_ = v_isSharedCheck_5664_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5657_);
                        crate::leanh::lean_dec(v___y_5655_);
                        v___x_5659_ = crate::leanh::lean_box(0);
                        v_isShared_5660_ = v_isSharedCheck_5664_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_5660_ == 0 {
                    v___x_5662_ = v___x_5659_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_a_5657_);
                    v___x_5662_ = v_reuseFailAlloc_5663_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(
    mut v_id_5676_: *mut crate::leanh::LeanObject,
    mut v_action_5677_: *mut crate::leanh::LeanObject,
    mut v_unknownIdentifierRanges_5678_: *mut crate::leanh::LeanObject,
    mut v_a_5679_: *mut crate::leanh::LeanObject,
    mut v_a_5680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5681_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
        v_id_5676_,
        v_action_5677_,
        v_unknownIdentifierRanges_5678_,
        v_a_5679_,
    );
    crate::leanh::lean_dec_ref(v_a_5679_);
    crate::leanh::lean_dec_ref(v_unknownIdentifierRanges_5678_);
    return v_res_5681_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(
    mut v_00_u03b2_5682_: *mut crate::leanh::LeanObject,
    mut v_m_5683_: *mut crate::leanh::LeanObject,
    mut v_a_5684_: *mut crate::leanh::LeanObject,
    mut v_b_5685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_5683_, v_a_5684_, v_b_5685_);
    return v___x_5686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(
    mut v_00_u03b2_5687_: *mut crate::leanh::LeanObject,
    mut v_m_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5690_: u8 = 0;
    v___x_5690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5688_, v_a_5689_);
    return v___x_5690_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(
    mut v_00_u03b2_5691_: *mut crate::leanh::LeanObject,
    mut v_m_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5694_: u8 = 0;
    let mut v_r_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5694_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_5691_, v_m_5692_, v_a_5693_);
    crate::leanh::lean_dec(v_a_5693_);
    crate::leanh::lean_dec_ref(v_m_5692_);
    v_r_5695_ = crate::leanh::lean_box((v_res_5694_) as usize);
    return v_r_5695_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(
    mut v___x_5696_: *mut crate::leanh::LeanObject,
    mut v_as_5697_: *mut crate::leanh::LeanObject,
    mut v_sz_5698_: usize,
    mut v_i_5699_: usize,
    mut v_b_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5696_, v_as_5697_, v_sz_5698_, v_i_5699_, v_b_5700_);
    return v___x_5703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(
    mut v___x_5704_: *mut crate::leanh::LeanObject,
    mut v_as_5705_: *mut crate::leanh::LeanObject,
    mut v_sz_5706_: *mut crate::leanh::LeanObject,
    mut v_i_5707_: *mut crate::leanh::LeanObject,
    mut v_b_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5711_: usize = 0;
    let mut v_i_boxed_5712_: usize = 0;
    let mut v_res_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5711_ = crate::leanh::lean_unbox_usize(v_sz_5706_);
    crate::leanh::lean_dec(v_sz_5706_);
    v_i_boxed_5712_ = crate::leanh::lean_unbox_usize(v_i_5707_);
    crate::leanh::lean_dec(v_i_5707_);
    v_res_5713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_5704_, v_as_5705_, v_sz_boxed_5711_, v_i_boxed_5712_, v_b_5708_, v___y_5709_);
    crate::leanh::lean_dec_ref(v___y_5709_);
    crate::leanh::lean_dec_ref(v_as_5705_);
    return v_res_5713_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(
    mut v_00_u03b2_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_x_5716_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5717_: u8 = 0;
    v___x_5717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5715_, v_x_5716_);
    return v___x_5717_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_5718_: *mut crate::leanh::LeanObject,
    mut v_a_5719_: *mut crate::leanh::LeanObject,
    mut v_x_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5721_: u8 = 0;
    let mut v_r_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_5718_, v_a_5719_, v_x_5720_);
    crate::leanh::lean_dec(v_x_5720_);
    crate::leanh::lean_dec(v_a_5719_);
    v_r_5722_ = crate::leanh::lean_box((v_res_5721_) as usize);
    return v_r_5722_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(
    mut v_00_u03b2_5723_: *mut crate::leanh::LeanObject,
    mut v_data_5724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_5724_);
    return v___x_5725_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5726_: *mut crate::leanh::LeanObject,
    mut v_i_5727_: *mut crate::leanh::LeanObject,
    mut v_source_5728_: *mut crate::leanh::LeanObject,
    mut v_target_5729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_5727_, v_source_5728_, v_target_5729_);
    return v___x_5730_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(
    mut v_00_u03b2_5731_: *mut crate::leanh::LeanObject,
    mut v_x_5732_: *mut crate::leanh::LeanObject,
    mut v_x_5733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_5732_, v_x_5733_);
    return v___x_5734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(
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
pub unsafe fn initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
}
