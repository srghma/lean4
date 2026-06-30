// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: Lean.Server.Completion.CompletionInfoSelection Lean.Server.CodeActions.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_eqv, lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_string_utf8_extract, lean_task_get_own, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f};
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
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_computeQueries___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_FileWorker_computeQueries___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_computeQueries___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
        ) as *mut leanh::LeanObject,
        2250887845330408536 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value
        ) as *mut leanh::LeanObject,
        16966433945472317273 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 98, 108, 105, 99, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 101, 116, 97, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 115, 101, 114, 118, 101, 114, 32, 114, 101, 113, 117, 101, 115, 116, 32, 114, 101, 115, 112, 111, 110, 115, 101, 58, 32, 0]};
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 104, 97, 110, 103, 101, 32, 116, 111, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 102, 114, 111, 109, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(
    mut v_r1_2868_: *mut leanh::LeanObject,
    mut v_r2_2869_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_start_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    v_start_2870_ = leanh::lean_ctor_get(v_r1_2868_, 0);
    v_stop_2871_ = leanh::lean_ctor_get(v_r1_2868_, 1);
    v_start_2872_ = leanh::lean_ctor_get(v_r2_2869_, 0);
    v_stop_2873_ = leanh::lean_ctor_get(v_r2_2869_, 1);
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
    mut v_r1_2883_: *mut leanh::LeanObject,
    mut v_r2_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2885_: u8 = 0;
    let mut v_r_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2885_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_r1_2883_, v_r2_2884_);
    leanh::lean_dec_ref(v_r2_2884_);
    leanh::lean_dec_ref(v_r1_2883_);
    v_r_2886_ = leanh::lean_box((v_res_2885_) as usize);
    return v_r_2886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(
    mut v_k_2887_: *mut leanh::LeanObject,
    mut v_t_2888_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2888_) == 0 {
                    v_k_2889_ = leanh::lean_ctor_get(v_t_2888_, 1);
                    v_l_2890_ = leanh::lean_ctor_get(v_t_2888_, 3);
                    v_r_2891_ = leanh::lean_ctor_get(v_t_2888_, 4);
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
    mut v_k_2897_: *mut leanh::LeanObject,
    mut v_t_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_2897_, v_t_2898_);
    leanh::lean_dec(v_t_2898_);
    leanh::lean_dec_ref(v_k_2897_);
    v_r_2900_ = leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(
    mut v_k_2901_: *mut leanh::LeanObject,
    mut v_v_2902_: *mut leanh::LeanObject,
    mut v_t_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v_impl_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_size_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_unused_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v_k_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v_unused_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_unused_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v_size_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_unused_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_unused_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v_k_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_unused_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_unused_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v_unused_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2903_) == 0 {
                    v_size_2904_ = leanh::lean_ctor_get(v_t_2903_, 0);
                    v_k_2905_ = leanh::lean_ctor_get(v_t_2903_, 1);
                    v_v_2906_ = leanh::lean_ctor_get(v_t_2903_, 2);
                    v_l_2907_ = leanh::lean_ctor_get(v_t_2903_, 3);
                    v_r_2908_ = leanh::lean_ctor_get(v_t_2903_, 4);
                    v_isSharedCheck_3188_ = (!leanh::lean_is_exclusive(v_t_2903_)) as u8;
                    if v_isSharedCheck_3188_ == 0 {
                        v___x_2910_ = v_t_2903_;
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2908_);
                        leanh::lean_inc(v_l_2907_);
                        leanh::lean_inc(v_v_2906_);
                        leanh::lean_inc(v_k_2905_);
                        leanh::lean_inc(v_size_2904_);
                        leanh::lean_dec(v_t_2903_);
                        v___x_2910_ = leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3189_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3190_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3190_, 0, v___x_3189_);
                    leanh::lean_ctor_set(v___x_3190_, 1, v_k_2901_);
                    leanh::lean_ctor_set(v___x_3190_, 2, v_v_2902_);
                    leanh::lean_ctor_set(v___x_3190_, 3, v_t_2903_);
                    leanh::lean_ctor_set(v___x_3190_, 4, v_t_2903_);
                    return v___x_3190_;
                }
            }
            1 => {
                v___x_2912_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_2901_, v_k_2905_);
                match v___x_2912_ {
                    0 => {
                        leanh::lean_dec(v_size_2904_);
                        v_impl_2913_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_l_2907_);
                        v___x_2914_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_2908_) == 0 {
                            v_size_2915_ = leanh::lean_ctor_get(v_r_2908_, 0);
                            v_size_2916_ = leanh::lean_ctor_get(v_impl_2913_, 0);
                            leanh::lean_inc(v_size_2916_);
                            v_k_2917_ = leanh::lean_ctor_get(v_impl_2913_, 1);
                            leanh::lean_inc(v_k_2917_);
                            v_v_2918_ = leanh::lean_ctor_get(v_impl_2913_, 2);
                            leanh::lean_inc(v_v_2918_);
                            v_l_2919_ = leanh::lean_ctor_get(v_impl_2913_, 3);
                            leanh::lean_inc(v_l_2919_);
                            v_r_2920_ = leanh::lean_ctor_get(v_impl_2913_, 4);
                            leanh::lean_inc(v_r_2920_);
                            v___x_2921_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2922_ = lean_nat_mul(v___x_2921_, v_size_2915_);
                            v___x_2923_ = lean_nat_dec_lt(v___x_2922_, v_size_2916_);
                            leanh::lean_dec(v___x_2922_);
                            if v___x_2923_ == 0 {
                                leanh::lean_dec(v_r_2920_);
                                leanh::lean_dec(v_l_2919_);
                                leanh::lean_dec(v_v_2918_);
                                leanh::lean_dec(v_k_2917_);
                                v___x_2924_ = lean_nat_add(v___x_2914_, v_size_2916_);
                                leanh::lean_dec(v_size_2916_);
                                v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2915_);
                                leanh::lean_dec(v___x_2924_);
                                if v_isShared_2911_ == 0 {
                                    leanh::lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_2925_);
                                    v___x_2927_ = v___x_2910_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2928_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        0,
                                        v___x_2925_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        1,
                                        v_k_2905_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        2,
                                        v_v_2906_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2928_,
                                        3,
                                        v_impl_2913_,
                                    );
                                    leanh::lean_ctor_set(
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
                                    (!leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_2994_ == 0 {
                                    v_unused_2995_ = leanh::lean_ctor_get(v_impl_2913_, 4);
                                    leanh::lean_dec(v_unused_2995_);
                                    v_unused_2996_ = leanh::lean_ctor_get(v_impl_2913_, 3);
                                    leanh::lean_dec(v_unused_2996_);
                                    v_unused_2997_ = leanh::lean_ctor_get(v_impl_2913_, 2);
                                    leanh::lean_dec(v_unused_2997_);
                                    v_unused_2998_ = leanh::lean_ctor_get(v_impl_2913_, 1);
                                    leanh::lean_dec(v_unused_2998_);
                                    v_unused_2999_ = leanh::lean_ctor_get(v_impl_2913_, 0);
                                    leanh::lean_dec(v_unused_2999_);
                                    v___x_2930_ = v_impl_2913_;
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2913_);
                                    v___x_2930_ = leanh::lean_box(0);
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3000_ = leanh::lean_ctor_get(v_impl_2913_, 3);
                            leanh::lean_inc(v_l_3000_);
                            if leanh::lean_obj_tag(v_l_3000_) == 0 {
                                v_r_3001_ = leanh::lean_ctor_get(v_impl_2913_, 4);
                                v_k_3002_ = leanh::lean_ctor_get(v_impl_2913_, 1);
                                v_v_3003_ = leanh::lean_ctor_get(v_impl_2913_, 2);
                                v_isSharedCheck_3014_ =
                                    (!leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_3014_ == 0 {
                                    v_unused_3015_ = leanh::lean_ctor_get(v_impl_2913_, 3);
                                    leanh::lean_dec(v_unused_3015_);
                                    v_unused_3016_ = leanh::lean_ctor_get(v_impl_2913_, 0);
                                    leanh::lean_dec(v_unused_3016_);
                                    v___x_3005_ = v_impl_2913_;
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_3001_);
                                    leanh::lean_inc(v_v_3003_);
                                    leanh::lean_inc(v_k_3002_);
                                    leanh::lean_dec(v_impl_2913_);
                                    v___x_3005_ = leanh::lean_box(0);
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3017_ = leanh::lean_ctor_get(v_impl_2913_, 4);
                                leanh::lean_inc(v_r_3017_);
                                if leanh::lean_obj_tag(v_r_3017_) == 0 {
                                    v_k_3018_ = leanh::lean_ctor_get(v_impl_2913_, 1);
                                    v_v_3019_ = leanh::lean_ctor_get(v_impl_2913_, 2);
                                    v_isSharedCheck_3042_ =
                                        (!leanh::lean_is_exclusive(v_impl_2913_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v_unused_3043_ =
                                            leanh::lean_ctor_get(v_impl_2913_, 4);
                                        leanh::lean_dec(v_unused_3043_);
                                        v_unused_3044_ =
                                            leanh::lean_ctor_get(v_impl_2913_, 3);
                                        leanh::lean_dec(v_unused_3044_);
                                        v_unused_3045_ =
                                            leanh::lean_ctor_get(v_impl_2913_, 0);
                                        leanh::lean_dec(v_unused_3045_);
                                        v___x_3021_ = v_impl_2913_;
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3019_);
                                        leanh::lean_inc(v_k_3018_);
                                        leanh::lean_dec(v_impl_2913_);
                                        v___x_3021_ = leanh::lean_box(0);
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3046_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        leanh::lean_ctor_set(v___x_2910_, 4, v_r_3017_);
                                        leanh::lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                        leanh::lean_ctor_set(v___x_2910_, 0, v___x_3046_);
                                        v___x_3048_ = v___x_2910_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3049_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            0,
                                            v___x_3046_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            1,
                                            v_k_2905_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            2,
                                            v_v_2906_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3049_,
                                            3,
                                            v_impl_2913_,
                                        );
                                        leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_v_2906_);
                        leanh::lean_dec(v_k_2905_);
                        if v_isShared_2911_ == 0 {
                            leanh::lean_ctor_set(v___x_2910_, 2, v_v_2902_);
                            leanh::lean_ctor_set(v___x_2910_, 1, v_k_2901_);
                            v___x_3051_ = v___x_2910_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3052_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_size_2904_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_k_2901_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_v_2902_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 3, v_l_2907_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 4, v_r_2908_);
                            v___x_3051_ = v_reuseFailAlloc_3052_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_2904_);
                        v_impl_3053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_r_2908_);
                        v___x_3054_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_2907_) == 0 {
                            v_size_3055_ = leanh::lean_ctor_get(v_l_2907_, 0);
                            v_size_3056_ = leanh::lean_ctor_get(v_impl_3053_, 0);
                            leanh::lean_inc(v_size_3056_);
                            v_k_3057_ = leanh::lean_ctor_get(v_impl_3053_, 1);
                            leanh::lean_inc(v_k_3057_);
                            v_v_3058_ = leanh::lean_ctor_get(v_impl_3053_, 2);
                            leanh::lean_inc(v_v_3058_);
                            v_l_3059_ = leanh::lean_ctor_get(v_impl_3053_, 3);
                            leanh::lean_inc(v_l_3059_);
                            v_r_3060_ = leanh::lean_ctor_get(v_impl_3053_, 4);
                            leanh::lean_inc(v_r_3060_);
                            v___x_3061_ = leanh::lean_unsigned_to_nat(3);
                            v___x_3062_ = lean_nat_mul(v___x_3061_, v_size_3055_);
                            v___x_3063_ = lean_nat_dec_lt(v___x_3062_, v_size_3056_);
                            leanh::lean_dec(v___x_3062_);
                            if v___x_3063_ == 0 {
                                leanh::lean_dec(v_r_3060_);
                                leanh::lean_dec(v_l_3059_);
                                leanh::lean_dec(v_v_3058_);
                                leanh::lean_dec(v_k_3057_);
                                v___x_3064_ = lean_nat_add(v___x_3054_, v_size_3055_);
                                v___x_3065_ = lean_nat_add(v___x_3064_, v_size_3056_);
                                leanh::lean_dec(v_size_3056_);
                                leanh::lean_dec(v___x_3064_);
                                if v_isShared_2911_ == 0 {
                                    leanh::lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3065_);
                                    v___x_3067_ = v___x_2910_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3068_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        0,
                                        v___x_3065_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        1,
                                        v_k_2905_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        2,
                                        v_v_2906_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3068_,
                                        3,
                                        v_l_2907_,
                                    );
                                    leanh::lean_ctor_set(
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
                                    (!leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3132_ == 0 {
                                    v_unused_3133_ = leanh::lean_ctor_get(v_impl_3053_, 4);
                                    leanh::lean_dec(v_unused_3133_);
                                    v_unused_3134_ = leanh::lean_ctor_get(v_impl_3053_, 3);
                                    leanh::lean_dec(v_unused_3134_);
                                    v_unused_3135_ = leanh::lean_ctor_get(v_impl_3053_, 2);
                                    leanh::lean_dec(v_unused_3135_);
                                    v_unused_3136_ = leanh::lean_ctor_get(v_impl_3053_, 1);
                                    leanh::lean_dec(v_unused_3136_);
                                    v_unused_3137_ = leanh::lean_ctor_get(v_impl_3053_, 0);
                                    leanh::lean_dec(v_unused_3137_);
                                    v___x_3070_ = v_impl_3053_;
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_3053_);
                                    v___x_3070_ = leanh::lean_box(0);
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3138_ = leanh::lean_ctor_get(v_impl_3053_, 3);
                            leanh::lean_inc(v_l_3138_);
                            if leanh::lean_obj_tag(v_l_3138_) == 0 {
                                v_r_3139_ = leanh::lean_ctor_get(v_impl_3053_, 4);
                                v_k_3140_ = leanh::lean_ctor_get(v_impl_3053_, 1);
                                v_v_3141_ = leanh::lean_ctor_get(v_impl_3053_, 2);
                                v_isSharedCheck_3164_ =
                                    (!leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3164_ == 0 {
                                    v_unused_3165_ = leanh::lean_ctor_get(v_impl_3053_, 3);
                                    leanh::lean_dec(v_unused_3165_);
                                    v_unused_3166_ = leanh::lean_ctor_get(v_impl_3053_, 0);
                                    leanh::lean_dec(v_unused_3166_);
                                    v___x_3143_ = v_impl_3053_;
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_3139_);
                                    leanh::lean_inc(v_v_3141_);
                                    leanh::lean_inc(v_k_3140_);
                                    leanh::lean_dec(v_impl_3053_);
                                    v___x_3143_ = leanh::lean_box(0);
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3167_ = leanh::lean_ctor_get(v_impl_3053_, 4);
                                leanh::lean_inc(v_r_3167_);
                                if leanh::lean_obj_tag(v_r_3167_) == 0 {
                                    v_k_3168_ = leanh::lean_ctor_get(v_impl_3053_, 1);
                                    v_v_3169_ = leanh::lean_ctor_get(v_impl_3053_, 2);
                                    v_isSharedCheck_3180_ =
                                        (!leanh::lean_is_exclusive(v_impl_3053_)) as u8;
                                    if v_isSharedCheck_3180_ == 0 {
                                        v_unused_3181_ =
                                            leanh::lean_ctor_get(v_impl_3053_, 4);
                                        leanh::lean_dec(v_unused_3181_);
                                        v_unused_3182_ =
                                            leanh::lean_ctor_get(v_impl_3053_, 3);
                                        leanh::lean_dec(v_unused_3182_);
                                        v_unused_3183_ =
                                            leanh::lean_ctor_get(v_impl_3053_, 0);
                                        leanh::lean_dec(v_unused_3183_);
                                        v___x_3171_ = v_impl_3053_;
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3169_);
                                        leanh::lean_inc(v_k_3168_);
                                        leanh::lean_dec(v_impl_3053_);
                                        v___x_3171_ = leanh::lean_box(0);
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3184_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        leanh::lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                        leanh::lean_ctor_set(v___x_2910_, 3, v_r_3167_);
                                        leanh::lean_ctor_set(v___x_2910_, 0, v___x_3184_);
                                        v___x_3186_ = v___x_2910_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3187_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            0,
                                            v___x_3184_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            1,
                                            v_k_2905_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            2,
                                            v_v_2906_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3187_,
                                            3,
                                            v_r_3167_,
                                        );
                                        leanh::lean_ctor_set(
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
                v_size_2932_ = leanh::lean_ctor_get(v_l_2919_, 0);
                v_size_2933_ = leanh::lean_ctor_get(v_r_2920_, 0);
                v_k_2934_ = leanh::lean_ctor_get(v_r_2920_, 1);
                v_v_2935_ = leanh::lean_ctor_get(v_r_2920_, 2);
                v_l_2936_ = leanh::lean_ctor_get(v_r_2920_, 3);
                v_r_2937_ = leanh::lean_ctor_get(v_r_2920_, 4);
                v___x_2938_ = leanh::lean_unsigned_to_nat(2);
                v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
                v___x_2940_ = lean_nat_dec_lt(v_size_2933_, v___x_2939_);
                leanh::lean_dec(v___x_2939_);
                if v___x_2940_ == 0 {
                    leanh::lean_inc(v_r_2937_);
                    leanh::lean_inc(v_l_2936_);
                    leanh::lean_inc(v_v_2935_);
                    leanh::lean_inc(v_k_2934_);
                    v_isSharedCheck_2969_ = (!leanh::lean_is_exclusive(v_r_2920_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v_unused_2970_ = leanh::lean_ctor_get(v_r_2920_, 4);
                        leanh::lean_dec(v_unused_2970_);
                        v_unused_2971_ = leanh::lean_ctor_get(v_r_2920_, 3);
                        leanh::lean_dec(v_unused_2971_);
                        v_unused_2972_ = leanh::lean_ctor_get(v_r_2920_, 2);
                        leanh::lean_dec(v_unused_2972_);
                        v_unused_2973_ = leanh::lean_ctor_get(v_r_2920_, 1);
                        leanh::lean_dec(v_unused_2973_);
                        v_unused_2974_ = leanh::lean_ctor_get(v_r_2920_, 0);
                        leanh::lean_dec(v_unused_2974_);
                        v___x_2942_ = v_r_2920_;
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2920_);
                        v___x_2942_ = leanh::lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2910_);
                    v___x_2975_ = lean_nat_add(v___x_2914_, v_size_2916_);
                    leanh::lean_dec(v_size_2916_);
                    v___x_2976_ = lean_nat_add(v___x_2975_, v_size_2915_);
                    leanh::lean_dec(v___x_2975_);
                    v___x_2977_ = lean_nat_add(v___x_2914_, v_size_2915_);
                    v___x_2978_ = lean_nat_add(v___x_2977_, v_size_2933_);
                    leanh::lean_dec(v___x_2977_);
                    leanh::lean_inc_ref(v_r_2908_);
                    if v_isShared_2931_ == 0 {
                        leanh::lean_ctor_set(v___x_2930_, 4, v_r_2908_);
                        leanh::lean_ctor_set(v___x_2930_, 3, v_r_2920_);
                        leanh::lean_ctor_set(v___x_2930_, 2, v_v_2906_);
                        leanh::lean_ctor_set(v___x_2930_, 1, v_k_2905_);
                        leanh::lean_ctor_set(v___x_2930_, 0, v___x_2978_);
                        v___x_2980_ = v___x_2930_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2978_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2905_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2906_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_r_2920_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_r_2908_);
                        v___x_2980_ = v_reuseFailAlloc_2993_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2944_ = lean_nat_add(v___x_2914_, v_size_2916_);
                leanh::lean_dec(v_size_2916_);
                v___x_2945_ = lean_nat_add(v___x_2944_, v_size_2915_);
                leanh::lean_dec(v___x_2944_);
                v___x_2957_ = lean_nat_add(v___x_2914_, v_size_2932_);
                if leanh::lean_obj_tag(v_l_2936_) == 0 {
                    v_size_2967_ = leanh::lean_ctor_get(v_l_2936_, 0);
                    leanh::lean_inc(v_size_2967_);
                    v___y_2959_ = v_size_2967_;
                    state = 8;
                    continue;
                } else {
                    v___x_2968_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2959_ = v___x_2968_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2950_ = lean_nat_add(v___y_2948_, v___y_2949_);
                leanh::lean_dec(v___y_2949_);
                leanh::lean_dec(v___y_2948_);
                if v_isShared_2943_ == 0 {
                    leanh::lean_ctor_set(v___x_2942_, 4, v_r_2908_);
                    leanh::lean_ctor_set(v___x_2942_, 3, v_r_2937_);
                    leanh::lean_ctor_set(v___x_2942_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v___x_2942_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v___x_2942_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_r_2937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_r_2908_);
                    v___x_2952_ = v_reuseFailAlloc_2956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2931_ == 0 {
                    leanh::lean_ctor_set(v___x_2930_, 4, v___x_2952_);
                    leanh::lean_ctor_set(v___x_2930_, 3, v___y_2947_);
                    leanh::lean_ctor_set(v___x_2930_, 2, v_v_2935_);
                    leanh::lean_ctor_set(v___x_2930_, 1, v_k_2934_);
                    leanh::lean_ctor_set(v___x_2930_, 0, v___x_2945_);
                    v___x_2954_ = v___x_2930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 3, v___y_2947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 4, v___x_2952_);
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
                leanh::lean_dec(v___y_2959_);
                leanh::lean_dec(v___x_2957_);
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v_l_2936_);
                    leanh::lean_ctor_set(v___x_2910_, 3, v_l_2919_);
                    leanh::lean_ctor_set(v___x_2910_, 2, v_v_2918_);
                    leanh::lean_ctor_set(v___x_2910_, 1, v_k_2917_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2910_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_l_2919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_l_2936_);
                    v___x_2962_ = v_reuseFailAlloc_2966_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2963_ = lean_nat_add(v___x_2914_, v_size_2915_);
                if leanh::lean_obj_tag(v_r_2937_) == 0 {
                    v_size_2964_ = leanh::lean_ctor_get(v_r_2937_, 0);
                    leanh::lean_inc(v_size_2964_);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v_size_2964_;
                    state = 5;
                    continue;
                } else {
                    v___x_2965_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v___x_2965_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2987_ = (!leanh::lean_is_exclusive(v_r_2908_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v_unused_2988_ = leanh::lean_ctor_get(v_r_2908_, 4);
                    leanh::lean_dec(v_unused_2988_);
                    v_unused_2989_ = leanh::lean_ctor_get(v_r_2908_, 3);
                    leanh::lean_dec(v_unused_2989_);
                    v_unused_2990_ = leanh::lean_ctor_get(v_r_2908_, 2);
                    leanh::lean_dec(v_unused_2990_);
                    v_unused_2991_ = leanh::lean_ctor_get(v_r_2908_, 1);
                    leanh::lean_dec(v_unused_2991_);
                    v_unused_2992_ = leanh::lean_ctor_get(v_r_2908_, 0);
                    leanh::lean_dec(v_unused_2992_);
                    v___x_2982_ = v_r_2908_;
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_2908_);
                    v___x_2982_ = leanh::lean_box(0);
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2983_ == 0 {
                    leanh::lean_ctor_set(v___x_2982_, 4, v___x_2980_);
                    leanh::lean_ctor_set(v___x_2982_, 3, v_l_2919_);
                    leanh::lean_ctor_set(v___x_2982_, 2, v_v_2918_);
                    leanh::lean_ctor_set(v___x_2982_, 1, v_k_2917_);
                    leanh::lean_ctor_set(v___x_2982_, 0, v___x_2976_);
                    v___x_2985_ = v___x_2982_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_l_2919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2985_;
            }
            13 => {
                v___x_3007_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_3001_);
                if v_isShared_3006_ == 0 {
                    leanh::lean_ctor_set(v___x_3005_, 3, v_r_3001_);
                    leanh::lean_ctor_set(v___x_3005_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v___x_3005_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v___x_3005_, 0, v___x_2914_);
                    v___x_3009_ = v___x_3005_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_r_3001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_r_3001_);
                    v___x_3009_ = v_reuseFailAlloc_3013_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v___x_3009_);
                    leanh::lean_ctor_set(v___x_2910_, 3, v_l_3000_);
                    leanh::lean_ctor_set(v___x_2910_, 2, v_v_3003_);
                    leanh::lean_ctor_set(v___x_2910_, 1, v_k_3002_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3007_);
                    v___x_3011_ = v___x_2910_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_3002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_3003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_3000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___x_3009_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3011_;
            }
            16 => {
                v_k_3023_ = leanh::lean_ctor_get(v_r_3017_, 1);
                v_v_3024_ = leanh::lean_ctor_get(v_r_3017_, 2);
                v_isSharedCheck_3038_ = (!leanh::lean_is_exclusive(v_r_3017_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v_unused_3039_ = leanh::lean_ctor_get(v_r_3017_, 4);
                    leanh::lean_dec(v_unused_3039_);
                    v_unused_3040_ = leanh::lean_ctor_get(v_r_3017_, 3);
                    leanh::lean_dec(v_unused_3040_);
                    v_unused_3041_ = leanh::lean_ctor_get(v_r_3017_, 0);
                    leanh::lean_dec(v_unused_3041_);
                    v___x_3026_ = v_r_3017_;
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3024_);
                    leanh::lean_inc(v_k_3023_);
                    leanh::lean_dec(v_r_3017_);
                    v___x_3026_ = leanh::lean_box(0);
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3028_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3027_ == 0 {
                    leanh::lean_ctor_set(v___x_3026_, 4, v_l_3000_);
                    leanh::lean_ctor_set(v___x_3026_, 3, v_l_3000_);
                    leanh::lean_ctor_set(v___x_3026_, 2, v_v_3019_);
                    leanh::lean_ctor_set(v___x_3026_, 1, v_k_3018_);
                    leanh::lean_ctor_set(v___x_3026_, 0, v___x_2914_);
                    v___x_3030_ = v___x_3026_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_2914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_k_3018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_v_3019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_l_3000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_l_3000_);
                    v___x_3030_ = v_reuseFailAlloc_3037_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3022_ == 0 {
                    leanh::lean_ctor_set(v___x_3021_, 4, v_l_3000_);
                    leanh::lean_ctor_set(v___x_3021_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v___x_3021_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v___x_3021_, 0, v___x_2914_);
                    v___x_3032_ = v___x_3021_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_3000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_l_3000_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v___x_3032_);
                    leanh::lean_ctor_set(v___x_2910_, 3, v___x_3030_);
                    leanh::lean_ctor_set(v___x_2910_, 2, v_v_3024_);
                    leanh::lean_ctor_set(v___x_2910_, 1, v_k_3023_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3028_);
                    v___x_3034_ = v___x_2910_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 3, v___x_3030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 4, v___x_3032_);
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
                v_size_3072_ = leanh::lean_ctor_get(v_l_3059_, 0);
                v_k_3073_ = leanh::lean_ctor_get(v_l_3059_, 1);
                v_v_3074_ = leanh::lean_ctor_get(v_l_3059_, 2);
                v_l_3075_ = leanh::lean_ctor_get(v_l_3059_, 3);
                v_r_3076_ = leanh::lean_ctor_get(v_l_3059_, 4);
                v_size_3077_ = leanh::lean_ctor_get(v_r_3060_, 0);
                v___x_3078_ = leanh::lean_unsigned_to_nat(2);
                v___x_3079_ = lean_nat_mul(v___x_3078_, v_size_3077_);
                v___x_3080_ = lean_nat_dec_lt(v_size_3072_, v___x_3079_);
                leanh::lean_dec(v___x_3079_);
                if v___x_3080_ == 0 {
                    leanh::lean_inc(v_r_3076_);
                    leanh::lean_inc(v_l_3075_);
                    leanh::lean_inc(v_v_3074_);
                    leanh::lean_inc(v_k_3073_);
                    v_isSharedCheck_3108_ = (!leanh::lean_is_exclusive(v_l_3059_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v_unused_3109_ = leanh::lean_ctor_get(v_l_3059_, 4);
                        leanh::lean_dec(v_unused_3109_);
                        v_unused_3110_ = leanh::lean_ctor_get(v_l_3059_, 3);
                        leanh::lean_dec(v_unused_3110_);
                        v_unused_3111_ = leanh::lean_ctor_get(v_l_3059_, 2);
                        leanh::lean_dec(v_unused_3111_);
                        v_unused_3112_ = leanh::lean_ctor_get(v_l_3059_, 1);
                        leanh::lean_dec(v_unused_3112_);
                        v_unused_3113_ = leanh::lean_ctor_get(v_l_3059_, 0);
                        leanh::lean_dec(v_unused_3113_);
                        v___x_3082_ = v_l_3059_;
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_3059_);
                        v___x_3082_ = leanh::lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2910_);
                    v___x_3114_ = lean_nat_add(v___x_3054_, v_size_3055_);
                    v___x_3115_ = lean_nat_add(v___x_3114_, v_size_3056_);
                    leanh::lean_dec(v_size_3056_);
                    v___x_3116_ = lean_nat_add(v___x_3114_, v_size_3072_);
                    leanh::lean_dec(v___x_3114_);
                    leanh::lean_inc_ref(v_l_2907_);
                    if v_isShared_3071_ == 0 {
                        leanh::lean_ctor_set(v___x_3070_, 4, v_l_3059_);
                        leanh::lean_ctor_set(v___x_3070_, 3, v_l_2907_);
                        leanh::lean_ctor_set(v___x_3070_, 2, v_v_2906_);
                        leanh::lean_ctor_set(v___x_3070_, 1, v_k_2905_);
                        leanh::lean_ctor_set(v___x_3070_, 0, v___x_3116_);
                        v___x_3118_ = v___x_3070_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3131_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3116_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_2905_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_2906_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_l_2907_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3059_);
                        v___x_3118_ = v_reuseFailAlloc_3131_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3084_ = lean_nat_add(v___x_3054_, v_size_3055_);
                v___x_3085_ = lean_nat_add(v___x_3084_, v_size_3056_);
                leanh::lean_dec(v_size_3056_);
                if leanh::lean_obj_tag(v_l_3075_) == 0 {
                    v_size_3106_ = leanh::lean_ctor_get(v_l_3075_, 0);
                    leanh::lean_inc(v_size_3106_);
                    v___y_3098_ = v_size_3106_;
                    state = 29;
                    continue;
                } else {
                    v___x_3107_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3098_ = v___x_3107_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3090_ = lean_nat_add(v___y_3087_, v___y_3089_);
                leanh::lean_dec(v___y_3089_);
                leanh::lean_dec(v___y_3087_);
                if v_isShared_3083_ == 0 {
                    leanh::lean_ctor_set(v___x_3082_, 4, v_r_3060_);
                    leanh::lean_ctor_set(v___x_3082_, 3, v_r_3076_);
                    leanh::lean_ctor_set(v___x_3082_, 2, v_v_3058_);
                    leanh::lean_ctor_set(v___x_3082_, 1, v_k_3057_);
                    leanh::lean_ctor_set(v___x_3082_, 0, v___x_3090_);
                    v___x_3092_ = v___x_3082_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_r_3076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_r_3060_);
                    v___x_3092_ = v_reuseFailAlloc_3096_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3071_ == 0 {
                    leanh::lean_ctor_set(v___x_3070_, 4, v___x_3092_);
                    leanh::lean_ctor_set(v___x_3070_, 3, v___y_3088_);
                    leanh::lean_ctor_set(v___x_3070_, 2, v_v_3074_);
                    leanh::lean_ctor_set(v___x_3070_, 1, v_k_3073_);
                    leanh::lean_ctor_set(v___x_3070_, 0, v___x_3085_);
                    v___x_3094_ = v___x_3070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_k_3073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_v_3074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 3, v___y_3088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 4, v___x_3092_);
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
                leanh::lean_dec(v___y_3098_);
                leanh::lean_dec(v___x_3084_);
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v_l_3075_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3099_);
                    v___x_3101_ = v___x_2910_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_l_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_l_3075_);
                    v___x_3101_ = v_reuseFailAlloc_3105_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3102_ = lean_nat_add(v___x_3054_, v_size_3077_);
                if leanh::lean_obj_tag(v_r_3076_) == 0 {
                    v_size_3103_ = leanh::lean_ctor_get(v_r_3076_, 0);
                    leanh::lean_inc(v_size_3103_);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v_size_3103_;
                    state = 26;
                    continue;
                } else {
                    v___x_3104_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v___x_3104_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3125_ = (!leanh::lean_is_exclusive(v_l_2907_)) as u8;
                if v_isSharedCheck_3125_ == 0 {
                    v_unused_3126_ = leanh::lean_ctor_get(v_l_2907_, 4);
                    leanh::lean_dec(v_unused_3126_);
                    v_unused_3127_ = leanh::lean_ctor_get(v_l_2907_, 3);
                    leanh::lean_dec(v_unused_3127_);
                    v_unused_3128_ = leanh::lean_ctor_get(v_l_2907_, 2);
                    leanh::lean_dec(v_unused_3128_);
                    v_unused_3129_ = leanh::lean_ctor_get(v_l_2907_, 1);
                    leanh::lean_dec(v_unused_3129_);
                    v_unused_3130_ = leanh::lean_ctor_get(v_l_2907_, 0);
                    leanh::lean_dec(v_unused_3130_);
                    v___x_3120_ = v_l_2907_;
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_2907_);
                    v___x_3120_ = leanh::lean_box(0);
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3121_ == 0 {
                    leanh::lean_ctor_set(v___x_3120_, 4, v_r_3060_);
                    leanh::lean_ctor_set(v___x_3120_, 3, v___x_3118_);
                    leanh::lean_ctor_set(v___x_3120_, 2, v_v_3058_);
                    leanh::lean_ctor_set(v___x_3120_, 1, v_k_3057_);
                    leanh::lean_ctor_set(v___x_3120_, 0, v___x_3115_);
                    v___x_3123_ = v___x_3120_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_k_3057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_v_3058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___x_3118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_r_3060_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3123_;
            }
            34 => {
                v_k_3145_ = leanh::lean_ctor_get(v_l_3138_, 1);
                v_v_3146_ = leanh::lean_ctor_get(v_l_3138_, 2);
                v_isSharedCheck_3160_ = (!leanh::lean_is_exclusive(v_l_3138_)) as u8;
                if v_isSharedCheck_3160_ == 0 {
                    v_unused_3161_ = leanh::lean_ctor_get(v_l_3138_, 4);
                    leanh::lean_dec(v_unused_3161_);
                    v_unused_3162_ = leanh::lean_ctor_get(v_l_3138_, 3);
                    leanh::lean_dec(v_unused_3162_);
                    v_unused_3163_ = leanh::lean_ctor_get(v_l_3138_, 0);
                    leanh::lean_dec(v_unused_3163_);
                    v___x_3148_ = v_l_3138_;
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3146_);
                    leanh::lean_inc(v_k_3145_);
                    leanh::lean_dec(v_l_3138_);
                    v___x_3148_ = leanh::lean_box(0);
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3150_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_3139_, 2);
                if v_isShared_3149_ == 0 {
                    leanh::lean_ctor_set(v___x_3148_, 4, v_r_3139_);
                    leanh::lean_ctor_set(v___x_3148_, 3, v_r_3139_);
                    leanh::lean_ctor_set(v___x_3148_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v___x_3148_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v___x_3148_, 0, v___x_3054_);
                    v___x_3152_ = v___x_3148_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_r_3139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_r_3139_);
                    v___x_3152_ = v_reuseFailAlloc_3159_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_3139_);
                if v_isShared_3144_ == 0 {
                    leanh::lean_ctor_set(v___x_3143_, 3, v_r_3139_);
                    leanh::lean_ctor_set(v___x_3143_, 0, v___x_3054_);
                    v___x_3154_ = v___x_3143_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_k_3140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_v_3141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_r_3139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_r_3139_);
                    v___x_3154_ = v_reuseFailAlloc_3158_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v___x_3154_);
                    leanh::lean_ctor_set(v___x_2910_, 3, v___x_3152_);
                    leanh::lean_ctor_set(v___x_2910_, 2, v_v_3146_);
                    leanh::lean_ctor_set(v___x_2910_, 1, v_k_3145_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3150_);
                    v___x_3156_ = v___x_2910_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_k_3145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_v_3146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 3, v___x_3152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 4, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3156_;
            }
            39 => {
                v___x_3173_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3172_ == 0 {
                    leanh::lean_ctor_set(v___x_3171_, 4, v_l_3138_);
                    leanh::lean_ctor_set(v___x_3171_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v___x_3171_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v___x_3171_, 0, v___x_3054_);
                    v___x_3175_ = v___x_3171_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_k_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_v_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_l_3138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_l_3138_);
                    v___x_3175_ = v_reuseFailAlloc_3179_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 4, v_r_3167_);
                    leanh::lean_ctor_set(v___x_2910_, 3, v___x_3175_);
                    leanh::lean_ctor_set(v___x_2910_, 2, v_v_3169_);
                    leanh::lean_ctor_set(v___x_2910_, 1, v_k_3168_);
                    leanh::lean_ctor_set(v___x_2910_, 0, v___x_3173_);
                    v___x_3177_ = v___x_2910_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_k_3168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_v_3169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 3, v___x_3175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_r_3167_);
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
    mut v_a_3191_: *mut leanh::LeanObject,
    mut v_as_3192_: *mut leanh::LeanObject,
    mut v_i_3193_: usize,
    mut v_stop_3194_: usize,
) -> u8 {
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3202_: *mut leanh::LeanObject,
    mut v_as_3203_: *mut leanh::LeanObject,
    mut v_i_3204_: *mut leanh::LeanObject,
    mut v_stop_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3206_: usize = 0;
    let mut v_stop_boxed_3207_: usize = 0;
    let mut v_res_3208_: u8 = 0;
    let mut v_r_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3206_ = leanh::lean_unbox_usize(v_i_3204_);
    leanh::lean_dec(v_i_3204_);
    v_stop_boxed_3207_ = leanh::lean_unbox_usize(v_stop_3205_);
    leanh::lean_dec(v_stop_3205_);
    v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_3202_, v_as_3203_, v_i_boxed_3206_, v_stop_boxed_3207_);
    leanh::lean_dec_ref(v_as_3203_);
    leanh::lean_dec_ref(v_a_3202_);
    v_r_3209_ = leanh::lean_box((v_res_3208_) as usize);
    return v_r_3209_;
}
pub unsafe fn l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
    mut v_as_3210_: *mut leanh::LeanObject,
    mut v_a_3211_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    v___x_3212_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_as_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3220_: u8 = 0;
    let mut v_r_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3220_ =
        l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
            v_as_3218_, v_a_3219_,
        );
    leanh::lean_dec_ref(v_a_3219_);
    leanh::lean_dec_ref(v_as_3218_);
    v_r_3221_ = leanh::lean_box((v_res_3220_) as usize);
    return v_r_3221_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
    mut v_ctx_3222_: *mut leanh::LeanObject,
    mut v_i_3223_: *mut leanh::LeanObject,
    mut v_acc_3224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_i_3223_) == 1 {
        let mut v_i_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: u8 = 0;
        let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_3225_ = leanh::lean_ctor_get(v_i_3223_, 0);
        v_toElabInfo_3226_ = leanh::lean_ctor_get(v_i_3225_, 0);
        v_expr_3227_ = leanh::lean_ctor_get(v_i_3225_, 3);
        v_stx_3228_ = leanh::lean_ctor_get(v_toElabInfo_3226_, 1);
        v___x_3229_ = 1;
        v___x_3230_ = l_Lean_Syntax_getRange_x3f(v_stx_3228_, v___x_3229_);
        if leanh::lean_obj_tag(v___x_3230_) == 1 {
            let mut v_val_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: u8 = 0;
            v_val_3231_ = leanh::lean_ctor_get(v___x_3230_, 0);
            leanh::lean_inc(v_val_3231_);
            leanh::lean_dec_ref_known(v___x_3230_, 1);
            v___x_3232_ = l_Lean_Expr_isFVar(v_expr_3227_);
            if v___x_3232_ == 0 {
                leanh::lean_dec(v_val_3231_);
                return v_acc_3224_;
            } else {
                let mut v_autoImplicits_3233_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_3234_: u8 = 0;
                v_autoImplicits_3233_ = leanh::lean_ctor_get(v_ctx_3222_, 2);
                v___x_3234_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(v_autoImplicits_3233_, v_expr_3227_);
                if v___x_3234_ == 0 {
                    leanh::lean_dec(v_val_3231_);
                    return v_acc_3224_;
                } else {
                    let mut v___x_3235_: u8 = 0;
                    v___x_3235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_val_3231_, v_acc_3224_);
                    if v___x_3235_ == 0 {
                        let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_3236_ = leanh::lean_box(0);
                        v___x_3237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_val_3231_, v___x_3236_, v_acc_3224_);
                        return v___x_3237_;
                    } else {
                        leanh::lean_dec(v_val_3231_);
                        return v_acc_3224_;
                    }
                }
            }
        } else {
            leanh::lean_dec(v___x_3230_);
            return v_acc_3224_;
        }
    } else {
        return v_acc_3224_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(
    mut v_ctx_3238_: *mut leanh::LeanObject,
    mut v_i_3239_: *mut leanh::LeanObject,
    mut v_acc_3240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
        v_ctx_3238_,
        v_i_3239_,
        v_acc_3240_,
    );
    leanh::lean_dec_ref(v_i_3239_);
    leanh::lean_dec_ref(v_ctx_3238_);
    return v_res_3241_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(
    mut v_x_3242_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    v___x_3243_ = l_Lean_unknownIdentifierMessageTag;
    v___x_3244_ = lean_name_eq(v_x_3242_, v___x_3243_);
    return v___x_3244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed(
    mut v_x_3245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3246_: u8 = 0;
    let mut v_r_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(v_x_3245_);
    leanh::lean_dec(v_x_3245_);
    v_r_3247_ = leanh::lean_box((v_res_3246_) as usize);
    return v_r_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(
    mut v_text_3249_: *mut leanh::LeanObject,
    mut v_requestedRange_3250_: *mut leanh::LeanObject,
    mut v_as_3251_: *mut leanh::LeanObject,
    mut v_sz_3252_: usize,
    mut v_i_3253_: usize,
    mut v_b_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: u8 = 0;
    let mut v_snd_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_a_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: usize = 0;
    let mut v___x_3272_: usize = 0;
    let mut v_reuseFailAlloc_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v_ranges_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut v_unused_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
                if v___x_3256_ == 0 {
                    return v_b_3254_;
                } else {
                    v_snd_3257_ = leanh::lean_ctor_get(v_b_3254_, 1);
                    v_isSharedCheck_3284_ = (!leanh::lean_is_exclusive(v_b_3254_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v_unused_3285_ = leanh::lean_ctor_get(v_b_3254_, 0);
                        leanh::lean_dec(v_unused_3285_);
                        v___x_3259_ = v_b_3254_;
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3257_);
                        leanh::lean_dec(v_b_3254_);
                        v___x_3259_ = leanh::lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3261_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
                v_pos_3262_ = leanh::lean_ctor_get(v_a_3261_, 1);
                v_endPos_3263_ = leanh::lean_ctor_get(v_a_3261_, 2);
                v_data_3264_ = leanh::lean_ctor_get(v_a_3261_, 4);
                v___f_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3266_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3264_);
                v___x_3275_ = l_Lean_MessageData_hasTag(v___f_3265_, v_data_3264_);
                if v___x_3275_ == 0 {
                    v_a_3268_ = v_snd_3257_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3262_);
                    v___x_3276_ = l_Lean_FileMap_ofPosition(v_text_3249_, v_pos_3262_);
                    if leanh::lean_obj_tag(v_endPos_3263_) == 0 {
                        leanh::lean_inc_ref(v_pos_3262_);
                        v___y_3278_ = v_pos_3262_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3283_ = leanh::lean_ctor_get(v_endPos_3263_, 0);
                        leanh::lean_inc(v_val_3283_);
                        v___y_3278_ = v_val_3283_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3260_ == 0 {
                    leanh::lean_ctor_set(v___x_3259_, 1, v_a_3268_);
                    leanh::lean_ctor_set(v___x_3259_, 0, v___x_3266_);
                    v___x_3270_ = v___x_3259_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_a_3268_);
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
                v_msgRange_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3280_, 0, v___x_3276_);
                leanh::lean_ctor_set(v_msgRange_3280_, 1, v___x_3279_);
                v___x_3281_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3280_,
                    v_requestedRange_3250_,
                    v___x_3275_,
                    v___x_3275_,
                );
                if v___x_3281_ == 0 {
                    leanh::lean_dec_ref_known(v_msgRange_3280_, 2);
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
    mut v_text_3286_: *mut leanh::LeanObject,
    mut v_requestedRange_3287_: *mut leanh::LeanObject,
    mut v_as_3288_: *mut leanh::LeanObject,
    mut v_sz_3289_: *mut leanh::LeanObject,
    mut v_i_3290_: *mut leanh::LeanObject,
    mut v_b_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3293_: usize = 0;
    let mut v_i_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3293_ = leanh::lean_unbox_usize(v_sz_3289_);
    leanh::lean_dec(v_sz_3289_);
    v_i_boxed_3294_ = leanh::lean_unbox_usize(v_i_3290_);
    leanh::lean_dec(v_i_3290_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_3286_, v_requestedRange_3287_, v_as_3288_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3291_);
    leanh::lean_dec_ref(v_as_3288_);
    leanh::lean_dec_ref(v_requestedRange_3287_);
    leanh::lean_dec_ref(v_text_3286_);
    return v_res_3295_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(
    mut v_text_3296_: *mut leanh::LeanObject,
    mut v_requestedRange_3297_: *mut leanh::LeanObject,
    mut v_as_3298_: *mut leanh::LeanObject,
    mut v_sz_3299_: usize,
    mut v_i_3300_: usize,
    mut v_b_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3303_: u8 = 0;
    let mut v_snd_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v_a_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: usize = 0;
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v_ranges_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_unused_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3303_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
                if v___x_3303_ == 0 {
                    return v_b_3301_;
                } else {
                    v_snd_3304_ = leanh::lean_ctor_get(v_b_3301_, 1);
                    v_isSharedCheck_3331_ = (!leanh::lean_is_exclusive(v_b_3301_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v_unused_3332_ = leanh::lean_ctor_get(v_b_3301_, 0);
                        leanh::lean_dec(v_unused_3332_);
                        v___x_3306_ = v_b_3301_;
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3304_);
                        leanh::lean_dec(v_b_3301_);
                        v___x_3306_ = leanh::lean_box(0);
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3308_ = lean_array_uget_borrowed(v_as_3298_, v_i_3300_);
                v_pos_3309_ = leanh::lean_ctor_get(v_a_3308_, 1);
                v_endPos_3310_ = leanh::lean_ctor_get(v_a_3308_, 2);
                v_data_3311_ = leanh::lean_ctor_get(v_a_3308_, 4);
                v___f_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3313_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3311_);
                v___x_3322_ = l_Lean_MessageData_hasTag(v___f_3312_, v_data_3311_);
                if v___x_3322_ == 0 {
                    v_a_3315_ = v_snd_3304_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3309_);
                    v___x_3323_ = l_Lean_FileMap_ofPosition(v_text_3296_, v_pos_3309_);
                    if leanh::lean_obj_tag(v_endPos_3310_) == 0 {
                        leanh::lean_inc_ref(v_pos_3309_);
                        v___y_3325_ = v_pos_3309_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3330_ = leanh::lean_ctor_get(v_endPos_3310_, 0);
                        leanh::lean_inc(v_val_3330_);
                        v___y_3325_ = v_val_3330_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3307_ == 0 {
                    leanh::lean_ctor_set(v___x_3306_, 1, v_a_3315_);
                    leanh::lean_ctor_set(v___x_3306_, 0, v___x_3313_);
                    v___x_3317_ = v___x_3306_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_a_3315_);
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
                v_msgRange_3327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3327_, 0, v___x_3323_);
                leanh::lean_ctor_set(v_msgRange_3327_, 1, v___x_3326_);
                v___x_3328_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3327_,
                    v_requestedRange_3297_,
                    v___x_3322_,
                    v___x_3322_,
                );
                if v___x_3328_ == 0 {
                    leanh::lean_dec_ref_known(v_msgRange_3327_, 2);
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
    mut v_text_3333_: *mut leanh::LeanObject,
    mut v_requestedRange_3334_: *mut leanh::LeanObject,
    mut v_as_3335_: *mut leanh::LeanObject,
    mut v_sz_3336_: *mut leanh::LeanObject,
    mut v_i_3337_: *mut leanh::LeanObject,
    mut v_b_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3340_: usize = 0;
    let mut v_i_boxed_3341_: usize = 0;
    let mut v_res_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3340_ = leanh::lean_unbox_usize(v_sz_3336_);
    leanh::lean_dec(v_sz_3336_);
    v_i_boxed_3341_ = leanh::lean_unbox_usize(v_i_3337_);
    leanh::lean_dec(v_i_3337_);
    v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3333_, v_requestedRange_3334_, v_as_3335_, v_sz_boxed_3340_, v_i_boxed_3341_, v_b_3338_);
    leanh::lean_dec_ref(v_as_3335_);
    leanh::lean_dec_ref(v_requestedRange_3334_);
    leanh::lean_dec_ref(v_text_3333_);
    return v_res_3342_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(
    mut v_init_3343_: *mut leanh::LeanObject,
    mut v_text_3344_: *mut leanh::LeanObject,
    mut v_requestedRange_3345_: *mut leanh::LeanObject,
    mut v_n_3346_: *mut leanh::LeanObject,
    mut v_b_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_n_3346_) == 0 {
        let mut v_cs_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3352_: usize = 0;
        let mut v___x_3353_: usize = 0;
        let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_3349_ = leanh::lean_ctor_get(v_n_3346_, 0);
        v___x_3350_ = leanh::lean_box(0);
        v___x_3351_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
        leanh::lean_ctor_set(v___x_3351_, 1, v_b_3347_);
        v_sz_3352_ = lean_array_size(v_cs_3349_);
        v___x_3353_ = 0usize;
        v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3343_, v_text_3344_, v_requestedRange_3345_, v_cs_3349_, v_sz_3352_, v___x_3353_, v___x_3351_);
        v_fst_3355_ = leanh::lean_ctor_get(v___x_3354_, 0);
        leanh::lean_inc(v_fst_3355_);
        if leanh::lean_obj_tag(v_fst_3355_) == 0 {
            let mut v_snd_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3356_ = leanh::lean_ctor_get(v___x_3354_, 1);
            leanh::lean_inc(v_snd_3356_);
            leanh::lean_dec_ref(v___x_3354_);
            v___x_3357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3357_, 0, v_snd_3356_);
            return v___x_3357_;
        } else {
            let mut v_val_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3354_);
            v_val_3358_ = leanh::lean_ctor_get(v_fst_3355_, 0);
            leanh::lean_inc(v_val_3358_);
            leanh::lean_dec_ref_known(v_fst_3355_, 1);
            return v_val_3358_;
        }
    } else {
        let mut v_vs_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3362_: usize = 0;
        let mut v___x_3363_: usize = 0;
        let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_3359_ = leanh::lean_ctor_get(v_n_3346_, 0);
        v___x_3360_ = leanh::lean_box(0);
        v___x_3361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3361_, 0, v___x_3360_);
        leanh::lean_ctor_set(v___x_3361_, 1, v_b_3347_);
        v_sz_3362_ = lean_array_size(v_vs_3359_);
        v___x_3363_ = 0usize;
        v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3344_, v_requestedRange_3345_, v_vs_3359_, v_sz_3362_, v___x_3363_, v___x_3361_);
        v_fst_3365_ = leanh::lean_ctor_get(v___x_3364_, 0);
        leanh::lean_inc(v_fst_3365_);
        if leanh::lean_obj_tag(v_fst_3365_) == 0 {
            let mut v_snd_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3366_ = leanh::lean_ctor_get(v___x_3364_, 1);
            leanh::lean_inc(v_snd_3366_);
            leanh::lean_dec_ref(v___x_3364_);
            v___x_3367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3367_, 0, v_snd_3366_);
            return v___x_3367_;
        } else {
            let mut v_val_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3364_);
            v_val_3368_ = leanh::lean_ctor_get(v_fst_3365_, 0);
            leanh::lean_inc(v_val_3368_);
            leanh::lean_dec_ref_known(v_fst_3365_, 1);
            return v_val_3368_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(
    mut v_init_3369_: *mut leanh::LeanObject,
    mut v_text_3370_: *mut leanh::LeanObject,
    mut v_requestedRange_3371_: *mut leanh::LeanObject,
    mut v_as_3372_: *mut leanh::LeanObject,
    mut v_sz_3373_: usize,
    mut v_i_3374_: usize,
    mut v_b_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3377_: u8 = 0;
    let mut v_snd_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v_a_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: usize = 0;
    let mut v___x_3393_: usize = 0;
    let mut v_reuseFailAlloc_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v_unused_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3377_ = lean_usize_dec_lt(v_i_3374_, v_sz_3373_);
                if v___x_3377_ == 0 {
                    return v_b_3375_;
                } else {
                    v_snd_3378_ = leanh::lean_ctor_get(v_b_3375_, 1);
                    v_isSharedCheck_3396_ = (!leanh::lean_is_exclusive(v_b_3375_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v_unused_3397_ = leanh::lean_ctor_get(v_b_3375_, 0);
                        leanh::lean_dec(v_unused_3397_);
                        v___x_3380_ = v_b_3375_;
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3378_);
                        leanh::lean_dec(v_b_3375_);
                        v___x_3380_ = leanh::lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3382_ = lean_array_uget_borrowed(v_as_3372_, v_i_3374_);
                leanh::lean_inc(v_snd_3378_);
                v___x_3383_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3369_, v_text_3370_, v_requestedRange_3371_, v_a_3382_, v_snd_3378_);
                if leanh::lean_obj_tag(v___x_3383_) == 0 {
                    v___x_3384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3384_, 0, v___x_3383_);
                    if v_isShared_3381_ == 0 {
                        leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3386_ = v___x_3380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3387_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3378_);
                        v___x_3386_ = v_reuseFailAlloc_3387_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3378_);
                    v_a_3388_ = leanh::lean_ctor_get(v___x_3383_, 0);
                    leanh::lean_inc(v_a_3388_);
                    leanh::lean_dec_ref_known(v___x_3383_, 1);
                    v___x_3389_ = leanh::lean_box(0);
                    if v_isShared_3381_ == 0 {
                        leanh::lean_ctor_set(v___x_3380_, 1, v_a_3388_);
                        leanh::lean_ctor_set(v___x_3380_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3380_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3395_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3389_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_a_3388_);
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
    mut v_init_3398_: *mut leanh::LeanObject,
    mut v_text_3399_: *mut leanh::LeanObject,
    mut v_requestedRange_3400_: *mut leanh::LeanObject,
    mut v_as_3401_: *mut leanh::LeanObject,
    mut v_sz_3402_: *mut leanh::LeanObject,
    mut v_i_3403_: *mut leanh::LeanObject,
    mut v_b_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3406_: usize = 0;
    let mut v_i_boxed_3407_: usize = 0;
    let mut v_res_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3406_ = leanh::lean_unbox_usize(v_sz_3402_);
    leanh::lean_dec(v_sz_3402_);
    v_i_boxed_3407_ = leanh::lean_unbox_usize(v_i_3403_);
    leanh::lean_dec(v_i_3403_);
    v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3398_, v_text_3399_, v_requestedRange_3400_, v_as_3401_, v_sz_boxed_3406_, v_i_boxed_3407_, v_b_3404_);
    leanh::lean_dec_ref(v_as_3401_);
    leanh::lean_dec_ref(v_requestedRange_3400_);
    leanh::lean_dec_ref(v_text_3399_);
    leanh::lean_dec_ref(v_init_3398_);
    return v_res_3408_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(
    mut v_init_3409_: *mut leanh::LeanObject,
    mut v_text_3410_: *mut leanh::LeanObject,
    mut v_requestedRange_3411_: *mut leanh::LeanObject,
    mut v_n_3412_: *mut leanh::LeanObject,
    mut v_b_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3409_, v_text_3410_, v_requestedRange_3411_, v_n_3412_, v_b_3413_);
    leanh::lean_dec_ref(v_n_3412_);
    leanh::lean_dec_ref(v_requestedRange_3411_);
    leanh::lean_dec_ref(v_text_3410_);
    leanh::lean_dec_ref(v_init_3409_);
    return v_res_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(
    mut v_text_3416_: *mut leanh::LeanObject,
    mut v_requestedRange_3417_: *mut leanh::LeanObject,
    mut v_as_3418_: *mut leanh::LeanObject,
    mut v_sz_3419_: usize,
    mut v_i_3420_: usize,
    mut v_b_3421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3423_: u8 = 0;
    let mut v_snd_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v_a_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: usize = 0;
    let mut v_reuseFailAlloc_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_ranges_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_unused_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3423_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
                if v___x_3423_ == 0 {
                    return v_b_3421_;
                } else {
                    v_snd_3424_ = leanh::lean_ctor_get(v_b_3421_, 1);
                    v_isSharedCheck_3451_ = (!leanh::lean_is_exclusive(v_b_3421_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v_unused_3452_ = leanh::lean_ctor_get(v_b_3421_, 0);
                        leanh::lean_dec(v_unused_3452_);
                        v___x_3426_ = v_b_3421_;
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3424_);
                        leanh::lean_dec(v_b_3421_);
                        v___x_3426_ = leanh::lean_box(0);
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3428_ = lean_array_uget_borrowed(v_as_3418_, v_i_3420_);
                v_pos_3429_ = leanh::lean_ctor_get(v_a_3428_, 1);
                v_endPos_3430_ = leanh::lean_ctor_get(v_a_3428_, 2);
                v_data_3431_ = leanh::lean_ctor_get(v_a_3428_, 4);
                v___f_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3433_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3431_);
                v___x_3442_ = l_Lean_MessageData_hasTag(v___f_3432_, v_data_3431_);
                if v___x_3442_ == 0 {
                    v_a_3435_ = v_snd_3424_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3429_);
                    v___x_3443_ = l_Lean_FileMap_ofPosition(v_text_3416_, v_pos_3429_);
                    if leanh::lean_obj_tag(v_endPos_3430_) == 0 {
                        leanh::lean_inc_ref(v_pos_3429_);
                        v___y_3445_ = v_pos_3429_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3450_ = leanh::lean_ctor_get(v_endPos_3430_, 0);
                        leanh::lean_inc(v_val_3450_);
                        v___y_3445_ = v_val_3450_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3427_ == 0 {
                    leanh::lean_ctor_set(v___x_3426_, 1, v_a_3435_);
                    leanh::lean_ctor_set(v___x_3426_, 0, v___x_3433_);
                    v___x_3437_ = v___x_3426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3435_);
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
                v_msgRange_3447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3447_, 0, v___x_3443_);
                leanh::lean_ctor_set(v_msgRange_3447_, 1, v___x_3446_);
                v___x_3448_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3447_,
                    v_requestedRange_3417_,
                    v___x_3442_,
                    v___x_3442_,
                );
                if v___x_3448_ == 0 {
                    leanh::lean_dec_ref_known(v_msgRange_3447_, 2);
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
    mut v_text_3453_: *mut leanh::LeanObject,
    mut v_requestedRange_3454_: *mut leanh::LeanObject,
    mut v_as_3455_: *mut leanh::LeanObject,
    mut v_sz_3456_: *mut leanh::LeanObject,
    mut v_i_3457_: *mut leanh::LeanObject,
    mut v_b_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3460_: usize = 0;
    let mut v_i_boxed_3461_: usize = 0;
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3460_ = leanh::lean_unbox_usize(v_sz_3456_);
    leanh::lean_dec(v_sz_3456_);
    v_i_boxed_3461_ = leanh::lean_unbox_usize(v_i_3457_);
    leanh::lean_dec(v_i_3457_);
    v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_3453_, v_requestedRange_3454_, v_as_3455_, v_sz_boxed_3460_, v_i_boxed_3461_, v_b_3458_);
    leanh::lean_dec_ref(v_as_3455_);
    leanh::lean_dec_ref(v_requestedRange_3454_);
    leanh::lean_dec_ref(v_text_3453_);
    return v_res_3462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(
    mut v_text_3463_: *mut leanh::LeanObject,
    mut v_requestedRange_3464_: *mut leanh::LeanObject,
    mut v_as_3465_: *mut leanh::LeanObject,
    mut v_sz_3466_: usize,
    mut v_i_3467_: usize,
    mut v_b_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3470_: u8 = 0;
    let mut v_snd_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_a_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v_ranges_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v_unused_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
                if v___x_3470_ == 0 {
                    return v_b_3468_;
                } else {
                    v_snd_3471_ = leanh::lean_ctor_get(v_b_3468_, 1);
                    v_isSharedCheck_3498_ = (!leanh::lean_is_exclusive(v_b_3468_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v_unused_3499_ = leanh::lean_ctor_get(v_b_3468_, 0);
                        leanh::lean_dec(v_unused_3499_);
                        v___x_3473_ = v_b_3468_;
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3471_);
                        leanh::lean_dec(v_b_3468_);
                        v___x_3473_ = leanh::lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3475_ = lean_array_uget_borrowed(v_as_3465_, v_i_3467_);
                v_pos_3476_ = leanh::lean_ctor_get(v_a_3475_, 1);
                v_endPos_3477_ = leanh::lean_ctor_get(v_a_3475_, 2);
                v_data_3478_ = leanh::lean_ctor_get(v_a_3475_, 4);
                v___f_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3480_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3478_);
                v___x_3489_ = l_Lean_MessageData_hasTag(v___f_3479_, v_data_3478_);
                if v___x_3489_ == 0 {
                    v_a_3482_ = v_snd_3471_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3476_);
                    v___x_3490_ = l_Lean_FileMap_ofPosition(v_text_3463_, v_pos_3476_);
                    if leanh::lean_obj_tag(v_endPos_3477_) == 0 {
                        leanh::lean_inc_ref(v_pos_3476_);
                        v___y_3492_ = v_pos_3476_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3497_ = leanh::lean_ctor_get(v_endPos_3477_, 0);
                        leanh::lean_inc(v_val_3497_);
                        v___y_3492_ = v_val_3497_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3474_ == 0 {
                    leanh::lean_ctor_set(v___x_3473_, 1, v_a_3482_);
                    leanh::lean_ctor_set(v___x_3473_, 0, v___x_3480_);
                    v___x_3484_ = v___x_3473_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_a_3482_);
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
                v_msgRange_3494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3494_, 0, v___x_3490_);
                leanh::lean_ctor_set(v_msgRange_3494_, 1, v___x_3493_);
                v___x_3495_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3494_,
                    v_requestedRange_3464_,
                    v___x_3489_,
                    v___x_3489_,
                );
                if v___x_3495_ == 0 {
                    leanh::lean_dec_ref_known(v_msgRange_3494_, 2);
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
    mut v_text_3500_: *mut leanh::LeanObject,
    mut v_requestedRange_3501_: *mut leanh::LeanObject,
    mut v_as_3502_: *mut leanh::LeanObject,
    mut v_sz_3503_: *mut leanh::LeanObject,
    mut v_i_3504_: *mut leanh::LeanObject,
    mut v_b_3505_: *mut leanh::LeanObject,
    mut v___y_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3507_: usize = 0;
    let mut v_i_boxed_3508_: usize = 0;
    let mut v_res_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3507_ = leanh::lean_unbox_usize(v_sz_3503_);
    leanh::lean_dec(v_sz_3503_);
    v_i_boxed_3508_ = leanh::lean_unbox_usize(v_i_3504_);
    leanh::lean_dec(v_i_3504_);
    v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3500_, v_requestedRange_3501_, v_as_3502_, v_sz_boxed_3507_, v_i_boxed_3508_, v_b_3505_);
    leanh::lean_dec_ref(v_as_3502_);
    leanh::lean_dec_ref(v_requestedRange_3501_);
    leanh::lean_dec_ref(v_text_3500_);
    return v_res_3509_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(
    mut v_text_3510_: *mut leanh::LeanObject,
    mut v_requestedRange_3511_: *mut leanh::LeanObject,
    mut v_t_3512_: *mut leanh::LeanObject,
    mut v_init_3513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_3515_ = leanh::lean_ctor_get(v_t_3512_, 0);
    v_tail_3516_ = leanh::lean_ctor_get(v_t_3512_, 1);
    leanh::lean_inc_ref(v_init_3513_);
    v___x_3517_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3513_, v_text_3510_, v_requestedRange_3511_, v_root_3515_, v_init_3513_);
    leanh::lean_dec_ref(v_init_3513_);
    if leanh::lean_obj_tag(v___x_3517_) == 0 {
        let mut v_a_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3518_ = leanh::lean_ctor_get(v___x_3517_, 0);
        leanh::lean_inc(v_a_3518_);
        leanh::lean_dec_ref_known(v___x_3517_, 1);
        return v_a_3518_;
    } else {
        let mut v_a_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3522_: usize = 0;
        let mut v___x_3523_: usize = 0;
        let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3519_ = leanh::lean_ctor_get(v___x_3517_, 0);
        leanh::lean_inc(v_a_3519_);
        leanh::lean_dec_ref_known(v___x_3517_, 1);
        v___x_3520_ = leanh::lean_box(0);
        v___x_3521_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3521_, 0, v___x_3520_);
        leanh::lean_ctor_set(v___x_3521_, 1, v_a_3519_);
        v_sz_3522_ = lean_array_size(v_tail_3516_);
        v___x_3523_ = 0usize;
        v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3510_, v_requestedRange_3511_, v_tail_3516_, v_sz_3522_, v___x_3523_, v___x_3521_);
        v_fst_3525_ = leanh::lean_ctor_get(v___x_3524_, 0);
        leanh::lean_inc(v_fst_3525_);
        if leanh::lean_obj_tag(v_fst_3525_) == 0 {
            let mut v_snd_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3526_ = leanh::lean_ctor_get(v___x_3524_, 1);
            leanh::lean_inc(v_snd_3526_);
            leanh::lean_dec_ref(v___x_3524_);
            return v_snd_3526_;
        } else {
            let mut v_val_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3524_);
            v_val_3527_ = leanh::lean_ctor_get(v_fst_3525_, 0);
            leanh::lean_inc(v_val_3527_);
            leanh::lean_dec_ref_known(v_fst_3525_, 1);
            return v_val_3527_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(
    mut v_text_3528_: *mut leanh::LeanObject,
    mut v_requestedRange_3529_: *mut leanh::LeanObject,
    mut v_t_3530_: *mut leanh::LeanObject,
    mut v_init_3531_: *mut leanh::LeanObject,
    mut v___y_3532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3528_, v_requestedRange_3529_, v_t_3530_, v_init_3531_);
    leanh::lean_dec_ref(v_t_3530_);
    leanh::lean_dec_ref(v_requestedRange_3529_);
    leanh::lean_dec_ref(v_text_3528_);
    return v_res_3533_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(
    mut v_init_3534_: *mut leanh::LeanObject,
    mut v_x_3535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3535_) == 0 {
                    v_k_3536_ = leanh::lean_ctor_get(v_x_3535_, 1);
                    leanh::lean_inc(v_k_3536_);
                    v_l_3537_ = leanh::lean_ctor_get(v_x_3535_, 3);
                    leanh::lean_inc(v_l_3537_);
                    v_r_3538_ = leanh::lean_ctor_get(v_x_3535_, 4);
                    leanh::lean_inc(v_r_3538_);
                    leanh::lean_dec_ref_known(v_x_3535_, 5);
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
    mut v_doc_3549_: *mut leanh::LeanObject,
    mut v_requestedRange_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: u8 = 0;
    let mut v___y_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_3552_ = leanh::lean_ctor_get(v_doc_3549_, 0);
                leanh::lean_inc_ref(v_toEditableDocumentCore_3552_);
                v_start_3553_ = leanh::lean_ctor_get(v_requestedRange_3550_, 0);
                leanh::lean_inc(v_start_3553_);
                v___x_3554_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_3549_, v_start_3553_);
                v___x_3555_ = lean_task_get_own(v___x_3554_);
                if leanh::lean_obj_tag(v___x_3555_) == 1 {
                    v_meta_3556_ = leanh::lean_ctor_get(v_toEditableDocumentCore_3552_, 0);
                    leanh::lean_inc_ref(v_meta_3556_);
                    leanh::lean_dec_ref(v_toEditableDocumentCore_3552_);
                    v_val_3557_ = leanh::lean_ctor_get(v___x_3555_, 0);
                    leanh::lean_inc(v_val_3557_);
                    leanh::lean_dec_ref_known(v___x_3555_, 1);
                    v_text_3558_ = leanh::lean_ctor_get(v_meta_3556_, 3);
                    leanh::lean_inc_ref(v_text_3558_);
                    leanh::lean_dec_ref(v_meta_3556_);
                    v_elabSnap_3559_ = leanh::lean_ctor_get(v_val_3557_, 3);
                    leanh::lean_inc_ref(v_elabSnap_3559_);
                    leanh::lean_dec(v_val_3557_);
                    v_tree_3560_ =
                        l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(
                            v_elabSnap_3559_,
                        );
                    leanh::lean_inc_ref(v_requestedRange_3550_);
                    leanh::lean_inc_ref(v_tree_3560_);
                    v___x_3561_ = l_Lean_Language_SnapshotTree_collectMessagesInRange(
                        v_tree_3560_,
                        v_requestedRange_3550_,
                    );
                    v_msgLog_3562_ = lean_task_get_own(v___x_3561_);
                    v_unreported_3563_ = leanh::lean_ctor_get(v_msgLog_3562_, 1);
                    leanh::lean_inc_ref(v_unreported_3563_);
                    leanh::lean_dec(v_msgLog_3562_);
                    v___x_3564_ = leanh::lean_unsigned_to_nat(0);
                    v_ranges_3565_ =
                        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                    v___x_3566_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3558_, v_requestedRange_3550_, v_unreported_3563_, v_ranges_3565_);
                    leanh::lean_dec_ref(v_unreported_3563_);
                    leanh::lean_dec_ref(v_text_3558_);
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
                    leanh::lean_dec(v___x_3555_);
                    leanh::lean_dec_ref(v_toEditableDocumentCore_3552_);
                    leanh::lean_dec_ref(v_requestedRange_3550_);
                    v___x_3587_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2;
                    return v___x_3587_;
                }
            }
            1 => {
                v___x_3571_ = lean_mk_empty_array_with_capacity(v___y_3570_);
                leanh::lean_dec(v___y_3570_);
                v___x_3572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3571_, v___y_3568_);
                v___x_3573_ = l_Array_append___redArg(v___x_3566_, v___x_3572_);
                leanh::lean_dec_ref(v___x_3572_);
                v___x_3574_ = leanh::lean_box((v___y_3569_) as usize);
                v___x_3575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                leanh::lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                return v___x_3575_;
            }
            2 => {
                v___x_3579_ = leanh::lean_box(1);
                v___x_3580_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(
                    v_tree_3560_,
                    v_requestedRange_3550_,
                    v___x_3579_,
                    v___f_3576_,
                );
                v___x_3581_ = lean_task_get_own(v___x_3580_);
                if leanh::lean_obj_tag(v___x_3581_) == 0 {
                    v_size_3582_ = leanh::lean_ctor_get(v___x_3581_, 0);
                    leanh::lean_inc(v_size_3582_);
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
    mut v_doc_3588_: *mut leanh::LeanObject,
    mut v_requestedRange_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ =
        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(v_doc_3588_, v_requestedRange_3589_);
    return v_res_3591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(
    mut v_00_u03b2_3592_: *mut leanh::LeanObject,
    mut v_k_3593_: *mut leanh::LeanObject,
    mut v_t_3594_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3595_: u8 = 0;
    v___x_3595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_3593_, v_t_3594_);
    return v___x_3595_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(
    mut v_00_u03b2_3596_: *mut leanh::LeanObject,
    mut v_k_3597_: *mut leanh::LeanObject,
    mut v_t_3598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3599_: u8 = 0;
    let mut v_r_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_00_u03b2_3596_, v_k_3597_, v_t_3598_);
    leanh::lean_dec(v_t_3598_);
    leanh::lean_dec_ref(v_k_3597_);
    v_r_3600_ = leanh::lean_box((v_res_3599_) as usize);
    return v_r_3600_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(
    mut v_00_u03b2_3601_: *mut leanh::LeanObject,
    mut v_k_3602_: *mut leanh::LeanObject,
    mut v_v_3603_: *mut leanh::LeanObject,
    mut v_t_3604_: *mut leanh::LeanObject,
    mut v_hl_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_3602_, v_v_3603_, v_t_3604_);
    return v___x_3606_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(
    mut v_init_3607_: *mut leanh::LeanObject,
    mut v_t_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_3607_, v_t_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(
    mut v_s_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ =
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0;
    v___x_3614_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3614_, 0, v_s_3612_);
    leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(
    mut v___f_3616_: *mut leanh::LeanObject,
    mut v_s_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v_firstCmdSnap_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_3618_ = leanh::lean_ctor_get(v_s_3617_, 0);
                leanh::lean_inc_ref(v_toSnapshot_3618_);
                v_metaSnap_3619_ = leanh::lean_ctor_get(v_s_3617_, 1);
                leanh::lean_inc_ref(v_metaSnap_3619_);
                v_result_x3f_3620_ = leanh::lean_ctor_get(v_s_3617_, 2);
                leanh::lean_inc(v_result_x3f_3620_);
                leanh::lean_dec_ref(v_s_3617_);
                if leanh::lean_obj_tag(v_result_x3f_3620_) == 0 {
                    v___x_3632_ = leanh::lean_box(0);
                    v___y_3622_ = v___x_3632_;
                    state = 1;
                    continue;
                } else {
                    v_val_3633_ = leanh::lean_ctor_get(v_result_x3f_3620_, 0);
                    v_isSharedCheck_3646_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_3620_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3635_ = v_result_x3f_3620_;
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3633_);
                        leanh::lean_dec(v_result_x3f_3620_);
                        v___x_3635_ = leanh::lean_box(0);
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_3623_ = leanh::lean_ctor_get(v_metaSnap_3619_, 0);
                leanh::lean_inc(v_stx_x3f_3623_);
                v_reportingRange_3624_ = leanh::lean_ctor_get(v_metaSnap_3619_, 1);
                leanh::lean_inc(v_reportingRange_3624_);
                v___x_3625_ = 1;
                v___x_3626_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_3619_,
                    v___f_3616_,
                    v_stx_x3f_3623_,
                    v_reportingRange_3624_,
                    v___x_3625_,
                );
                v___x_3627_ = leanh::lean_unsigned_to_nat(1);
                v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
                v___x_3629_ = lean_array_push(v___x_3628_, v___x_3626_);
                v___x_3630_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_3622_, v___x_3629_);
                v___x_3631_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3631_, 0, v_toSnapshot_3618_);
                leanh::lean_ctor_set(v___x_3631_, 1, v___x_3630_);
                return v___x_3631_;
            }
            2 => {
                v_firstCmdSnap_3637_ = leanh::lean_ctor_get(v_val_3633_, 1);
                leanh::lean_inc_ref(v_firstCmdSnap_3637_);
                leanh::lean_dec(v_val_3633_);
                v_stx_x3f_3638_ = leanh::lean_ctor_get(v_firstCmdSnap_3637_, 0);
                leanh::lean_inc(v_stx_x3f_3638_);
                v_reportingRange_3639_ = leanh::lean_ctor_get(v_firstCmdSnap_3637_, 1);
                leanh::lean_inc(v_reportingRange_3639_);
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
                    leanh::lean_ctor_set(v___x_3635_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
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
    mut v_as_3647_: *mut leanh::LeanObject,
    mut v_i_3648_: usize,
    mut v_stop_3649_: usize,
    mut v_b_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3651_: u8 = 0;
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = lean_usize_dec_eq(v_i_3648_, v_stop_3649_);
                if v___x_3651_ == 0 {
                    v___x_3652_ = lean_array_uget_borrowed(v_as_3647_, v_i_3648_);
                    leanh::lean_inc(v___x_3652_);
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
    mut v_as_3657_: *mut leanh::LeanObject,
    mut v_i_3658_: *mut leanh::LeanObject,
    mut v_stop_3659_: *mut leanh::LeanObject,
    mut v_b_3660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3661_: usize = 0;
    let mut v_stop_boxed_3662_: usize = 0;
    let mut v_res_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3661_ = leanh::lean_unbox_usize(v_i_3658_);
    leanh::lean_dec(v_i_3658_);
    v_stop_boxed_3662_ = leanh::lean_unbox_usize(v_stop_3659_);
    leanh::lean_dec(v_stop_3659_);
    v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v_as_3657_, v_i_boxed_3661_, v_stop_boxed_3662_, v_b_3660_);
    leanh::lean_dec_ref(v_as_3657_);
    return v_res_3663_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(
    mut v_as_x27_3664_: *mut leanh::LeanObject,
    mut v_b_3665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3664_) == 0 {
                    return v_b_3665_;
                } else {
                    v_head_3667_ = leanh::lean_ctor_get(v_as_x27_3664_, 0);
                    v_tail_3668_ = leanh::lean_ctor_get(v_as_x27_3664_, 1);
                    v___f_3669_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3670_ = leanh::lean_box(1);
                    leanh::lean_inc(v_head_3667_);
                    v___x_3671_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3667_);
                    v___x_3672_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3669_,
                        v___x_3670_,
                        v___x_3671_,
                    );
                    if leanh::lean_obj_tag(v___x_3672_) == 0 {
                        v_size_3679_ = leanh::lean_ctor_get(v___x_3672_, 0);
                        leanh::lean_inc(v_size_3679_);
                        v___y_3674_ = v_size_3679_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3680_ = leanh::lean_unsigned_to_nat(0);
                        v___y_3674_ = v___x_3680_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3675_ = lean_mk_empty_array_with_capacity(v___y_3674_);
                leanh::lean_dec(v___y_3674_);
                v___x_3676_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3675_, v___x_3672_);
                v___x_3677_ = l_Array_append___redArg(v_b_3665_, v___x_3676_);
                leanh::lean_dec_ref(v___x_3676_);
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
    mut v_as_x27_3681_: *mut leanh::LeanObject,
    mut v_b_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_3681_, v_b_3682_);
    leanh::lean_dec(v_as_x27_3681_);
    return v_res_3684_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(
    mut v_as_3685_: *mut leanh::LeanObject,
    mut v_as_x27_3686_: *mut leanh::LeanObject,
    mut v_b_3687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3686_) == 0 {
                    return v_b_3687_;
                } else {
                    v_head_3689_ = leanh::lean_ctor_get(v_as_x27_3686_, 0);
                    v_tail_3690_ = leanh::lean_ctor_get(v_as_x27_3686_, 1);
                    v___f_3691_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3692_ = leanh::lean_box(1);
                    leanh::lean_inc(v_head_3689_);
                    v___x_3693_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3689_);
                    v___x_3694_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3691_,
                        v___x_3692_,
                        v___x_3693_,
                    );
                    if leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_size_3701_ = leanh::lean_ctor_get(v___x_3694_, 0);
                        leanh::lean_inc(v_size_3701_);
                        v___y_3696_ = v_size_3701_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3702_ = leanh::lean_unsigned_to_nat(0);
                        v___y_3696_ = v___x_3702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3697_ = lean_mk_empty_array_with_capacity(v___y_3696_);
                leanh::lean_dec(v___y_3696_);
                v___x_3698_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3697_, v___x_3694_);
                v___x_3699_ = l_Array_append___redArg(v_b_3687_, v___x_3698_);
                leanh::lean_dec_ref(v___x_3698_);
                v___x_3700_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_tail_3690_, v___x_3699_);
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(
    mut v_as_3703_: *mut leanh::LeanObject,
    mut v_as_x27_3704_: *mut leanh::LeanObject,
    mut v_b_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_3703_, v_as_x27_3704_, v_b_3705_);
    leanh::lean_dec(v_as_x27_3704_);
    leanh::lean_dec(v_as_3703_);
    return v_res_3707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(
    mut v_text_3708_: *mut leanh::LeanObject,
    mut v_as_3709_: *mut leanh::LeanObject,
    mut v_sz_3710_: usize,
    mut v_i_3711_: usize,
    mut v_b_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3714_: u8 = 0;
    let mut v_snd_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v_a_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: usize = 0;
    let mut v_reuseFailAlloc_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_unused_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3714_ = lean_usize_dec_lt(v_i_3711_, v_sz_3710_);
                if v___x_3714_ == 0 {
                    return v_b_3712_;
                } else {
                    v_snd_3715_ = leanh::lean_ctor_get(v_b_3712_, 1);
                    v_isSharedCheck_3741_ = (!leanh::lean_is_exclusive(v_b_3712_)) as u8;
                    if v_isSharedCheck_3741_ == 0 {
                        v_unused_3742_ = leanh::lean_ctor_get(v_b_3712_, 0);
                        leanh::lean_dec(v_unused_3742_);
                        v___x_3717_ = v_b_3712_;
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3715_);
                        leanh::lean_dec(v_b_3712_);
                        v___x_3717_ = leanh::lean_box(0);
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3719_ = lean_array_uget_borrowed(v_as_3709_, v_i_3711_);
                v_pos_3720_ = leanh::lean_ctor_get(v_a_3719_, 1);
                v_endPos_3721_ = leanh::lean_ctor_get(v_a_3719_, 2);
                v_data_3722_ = leanh::lean_ctor_get(v_a_3719_, 4);
                v___f_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3724_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3722_);
                v___x_3733_ = l_Lean_MessageData_hasTag(v___f_3723_, v_data_3722_);
                if v___x_3733_ == 0 {
                    v_a_3726_ = v_snd_3715_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3720_);
                    v___x_3734_ = l_Lean_FileMap_ofPosition(v_text_3708_, v_pos_3720_);
                    if leanh::lean_obj_tag(v_endPos_3721_) == 0 {
                        leanh::lean_inc_ref(v_pos_3720_);
                        v___y_3736_ = v_pos_3720_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3740_ = leanh::lean_ctor_get(v_endPos_3721_, 0);
                        leanh::lean_inc(v_val_3740_);
                        v___y_3736_ = v_val_3740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3718_ == 0 {
                    leanh::lean_ctor_set(v___x_3717_, 1, v_a_3726_);
                    leanh::lean_ctor_set(v___x_3717_, 0, v___x_3724_);
                    v___x_3728_ = v___x_3717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_a_3726_);
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
                v_msgRange_3738_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3738_, 0, v___x_3734_);
                leanh::lean_ctor_set(v_msgRange_3738_, 1, v___x_3737_);
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
    mut v_text_3743_: *mut leanh::LeanObject,
    mut v_as_3744_: *mut leanh::LeanObject,
    mut v_sz_3745_: *mut leanh::LeanObject,
    mut v_i_3746_: *mut leanh::LeanObject,
    mut v_b_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3749_: usize = 0;
    let mut v_i_boxed_3750_: usize = 0;
    let mut v_res_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3749_ = leanh::lean_unbox_usize(v_sz_3745_);
    leanh::lean_dec(v_sz_3745_);
    v_i_boxed_3750_ = leanh::lean_unbox_usize(v_i_3746_);
    leanh::lean_dec(v_i_3746_);
    v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_3743_, v_as_3744_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3747_);
    leanh::lean_dec_ref(v_as_3744_);
    leanh::lean_dec_ref(v_text_3743_);
    return v_res_3751_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(
    mut v_text_3752_: *mut leanh::LeanObject,
    mut v_as_3753_: *mut leanh::LeanObject,
    mut v_sz_3754_: usize,
    mut v_i_3755_: usize,
    mut v_b_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3758_: u8 = 0;
    let mut v_snd_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_a_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: usize = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
                if v___x_3758_ == 0 {
                    return v_b_3756_;
                } else {
                    v_snd_3759_ = leanh::lean_ctor_get(v_b_3756_, 1);
                    v_isSharedCheck_3785_ = (!leanh::lean_is_exclusive(v_b_3756_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v_unused_3786_ = leanh::lean_ctor_get(v_b_3756_, 0);
                        leanh::lean_dec(v_unused_3786_);
                        v___x_3761_ = v_b_3756_;
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3759_);
                        leanh::lean_dec(v_b_3756_);
                        v___x_3761_ = leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3763_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
                v_pos_3764_ = leanh::lean_ctor_get(v_a_3763_, 1);
                v_endPos_3765_ = leanh::lean_ctor_get(v_a_3763_, 2);
                v_data_3766_ = leanh::lean_ctor_get(v_a_3763_, 4);
                v___f_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3768_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3766_);
                v___x_3777_ = l_Lean_MessageData_hasTag(v___f_3767_, v_data_3766_);
                if v___x_3777_ == 0 {
                    v_a_3770_ = v_snd_3759_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3764_);
                    v___x_3778_ = l_Lean_FileMap_ofPosition(v_text_3752_, v_pos_3764_);
                    if leanh::lean_obj_tag(v_endPos_3765_) == 0 {
                        leanh::lean_inc_ref(v_pos_3764_);
                        v___y_3780_ = v_pos_3764_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3784_ = leanh::lean_ctor_get(v_endPos_3765_, 0);
                        leanh::lean_inc(v_val_3784_);
                        v___y_3780_ = v_val_3784_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3762_ == 0 {
                    leanh::lean_ctor_set(v___x_3761_, 1, v_a_3770_);
                    leanh::lean_ctor_set(v___x_3761_, 0, v___x_3768_);
                    v___x_3772_ = v___x_3761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_a_3770_);
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
                v_msgRange_3782_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3782_, 0, v___x_3778_);
                leanh::lean_ctor_set(v_msgRange_3782_, 1, v___x_3781_);
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
    mut v_text_3787_: *mut leanh::LeanObject,
    mut v_as_3788_: *mut leanh::LeanObject,
    mut v_sz_3789_: *mut leanh::LeanObject,
    mut v_i_3790_: *mut leanh::LeanObject,
    mut v_b_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3793_: usize = 0;
    let mut v_i_boxed_3794_: usize = 0;
    let mut v_res_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3793_ = leanh::lean_unbox_usize(v_sz_3789_);
    leanh::lean_dec(v_sz_3789_);
    v_i_boxed_3794_ = leanh::lean_unbox_usize(v_i_3790_);
    leanh::lean_dec(v_i_3790_);
    v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3787_, v_as_3788_, v_sz_boxed_3793_, v_i_boxed_3794_, v_b_3791_);
    leanh::lean_dec_ref(v_as_3788_);
    leanh::lean_dec_ref(v_text_3787_);
    return v_res_3795_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(
    mut v_text_3796_: *mut leanh::LeanObject,
    mut v_as_3797_: *mut leanh::LeanObject,
    mut v_sz_3798_: usize,
    mut v_i_3799_: usize,
    mut v_b_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: u8 = 0;
    let mut v_snd_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_a_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: usize = 0;
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_unused_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
                if v___x_3802_ == 0 {
                    return v_b_3800_;
                } else {
                    v_snd_3803_ = leanh::lean_ctor_get(v_b_3800_, 1);
                    v_isSharedCheck_3829_ = (!leanh::lean_is_exclusive(v_b_3800_)) as u8;
                    if v_isSharedCheck_3829_ == 0 {
                        v_unused_3830_ = leanh::lean_ctor_get(v_b_3800_, 0);
                        leanh::lean_dec(v_unused_3830_);
                        v___x_3805_ = v_b_3800_;
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3803_);
                        leanh::lean_dec(v_b_3800_);
                        v___x_3805_ = leanh::lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3807_ = lean_array_uget_borrowed(v_as_3797_, v_i_3799_);
                v_pos_3808_ = leanh::lean_ctor_get(v_a_3807_, 1);
                v_endPos_3809_ = leanh::lean_ctor_get(v_a_3807_, 2);
                v_data_3810_ = leanh::lean_ctor_get(v_a_3807_, 4);
                v___f_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3812_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3810_);
                v___x_3821_ = l_Lean_MessageData_hasTag(v___f_3811_, v_data_3810_);
                if v___x_3821_ == 0 {
                    v_a_3814_ = v_snd_3803_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3808_);
                    v___x_3822_ = l_Lean_FileMap_ofPosition(v_text_3796_, v_pos_3808_);
                    if leanh::lean_obj_tag(v_endPos_3809_) == 0 {
                        leanh::lean_inc_ref(v_pos_3808_);
                        v___y_3824_ = v_pos_3808_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3828_ = leanh::lean_ctor_get(v_endPos_3809_, 0);
                        leanh::lean_inc(v_val_3828_);
                        v___y_3824_ = v_val_3828_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3806_ == 0 {
                    leanh::lean_ctor_set(v___x_3805_, 1, v_a_3814_);
                    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3812_);
                    v___x_3816_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3814_);
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
                v_msgRange_3826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3826_, 0, v___x_3822_);
                leanh::lean_ctor_set(v_msgRange_3826_, 1, v___x_3825_);
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
    mut v_text_3831_: *mut leanh::LeanObject,
    mut v_as_3832_: *mut leanh::LeanObject,
    mut v_sz_3833_: *mut leanh::LeanObject,
    mut v_i_3834_: *mut leanh::LeanObject,
    mut v_b_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3837_: usize = 0;
    let mut v_i_boxed_3838_: usize = 0;
    let mut v_res_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3837_ = leanh::lean_unbox_usize(v_sz_3833_);
    leanh::lean_dec(v_sz_3833_);
    v_i_boxed_3838_ = leanh::lean_unbox_usize(v_i_3834_);
    leanh::lean_dec(v_i_3834_);
    v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_3831_, v_as_3832_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3835_);
    leanh::lean_dec_ref(v_as_3832_);
    leanh::lean_dec_ref(v_text_3831_);
    return v_res_3839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(
    mut v_text_3840_: *mut leanh::LeanObject,
    mut v_as_3841_: *mut leanh::LeanObject,
    mut v_sz_3842_: usize,
    mut v_i_3843_: usize,
    mut v_b_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3846_: u8 = 0;
    let mut v_snd_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v_a_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: usize = 0;
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_unused_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3846_ = lean_usize_dec_lt(v_i_3843_, v_sz_3842_);
                if v___x_3846_ == 0 {
                    return v_b_3844_;
                } else {
                    v_snd_3847_ = leanh::lean_ctor_get(v_b_3844_, 1);
                    v_isSharedCheck_3873_ = (!leanh::lean_is_exclusive(v_b_3844_)) as u8;
                    if v_isSharedCheck_3873_ == 0 {
                        v_unused_3874_ = leanh::lean_ctor_get(v_b_3844_, 0);
                        leanh::lean_dec(v_unused_3874_);
                        v___x_3849_ = v_b_3844_;
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3847_);
                        leanh::lean_dec(v_b_3844_);
                        v___x_3849_ = leanh::lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3851_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
                v_pos_3852_ = leanh::lean_ctor_get(v_a_3851_, 1);
                v_endPos_3853_ = leanh::lean_ctor_get(v_a_3851_, 2);
                v_data_3854_ = leanh::lean_ctor_get(v_a_3851_, 4);
                v___f_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3856_ = leanh::lean_box(0);
                leanh::lean_inc(v_data_3854_);
                v___x_3865_ = l_Lean_MessageData_hasTag(v___f_3855_, v_data_3854_);
                if v___x_3865_ == 0 {
                    v_a_3858_ = v_snd_3847_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_pos_3852_);
                    v___x_3866_ = l_Lean_FileMap_ofPosition(v_text_3840_, v_pos_3852_);
                    if leanh::lean_obj_tag(v_endPos_3853_) == 0 {
                        leanh::lean_inc_ref(v_pos_3852_);
                        v___y_3868_ = v_pos_3852_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3872_ = leanh::lean_ctor_get(v_endPos_3853_, 0);
                        leanh::lean_inc(v_val_3872_);
                        v___y_3868_ = v_val_3872_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3850_ == 0 {
                    leanh::lean_ctor_set(v___x_3849_, 1, v_a_3858_);
                    leanh::lean_ctor_set(v___x_3849_, 0, v___x_3856_);
                    v___x_3860_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_a_3858_);
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
                v_msgRange_3870_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgRange_3870_, 0, v___x_3866_);
                leanh::lean_ctor_set(v_msgRange_3870_, 1, v___x_3869_);
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
    mut v_text_3875_: *mut leanh::LeanObject,
    mut v_as_3876_: *mut leanh::LeanObject,
    mut v_sz_3877_: *mut leanh::LeanObject,
    mut v_i_3878_: *mut leanh::LeanObject,
    mut v_b_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3881_: usize = 0;
    let mut v_i_boxed_3882_: usize = 0;
    let mut v_res_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3881_ = leanh::lean_unbox_usize(v_sz_3877_);
    leanh::lean_dec(v_sz_3877_);
    v_i_boxed_3882_ = leanh::lean_unbox_usize(v_i_3878_);
    leanh::lean_dec(v_i_3878_);
    v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3875_, v_as_3876_, v_sz_boxed_3881_, v_i_boxed_3882_, v_b_3879_);
    leanh::lean_dec_ref(v_as_3876_);
    leanh::lean_dec_ref(v_text_3875_);
    return v_res_3883_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(
    mut v_init_3884_: *mut leanh::LeanObject,
    mut v_text_3885_: *mut leanh::LeanObject,
    mut v_n_3886_: *mut leanh::LeanObject,
    mut v_b_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_n_3886_) == 0 {
        let mut v_cs_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3892_: usize = 0;
        let mut v___x_3893_: usize = 0;
        let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_3889_ = leanh::lean_ctor_get(v_n_3886_, 0);
        v___x_3890_ = leanh::lean_box(0);
        v___x_3891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3891_, 0, v___x_3890_);
        leanh::lean_ctor_set(v___x_3891_, 1, v_b_3887_);
        v_sz_3892_ = lean_array_size(v_cs_3889_);
        v___x_3893_ = 0usize;
        v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3884_, v_text_3885_, v_cs_3889_, v_sz_3892_, v___x_3893_, v___x_3891_);
        v_fst_3895_ = leanh::lean_ctor_get(v___x_3894_, 0);
        leanh::lean_inc(v_fst_3895_);
        if leanh::lean_obj_tag(v_fst_3895_) == 0 {
            let mut v_snd_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3896_ = leanh::lean_ctor_get(v___x_3894_, 1);
            leanh::lean_inc(v_snd_3896_);
            leanh::lean_dec_ref(v___x_3894_);
            v___x_3897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3897_, 0, v_snd_3896_);
            return v___x_3897_;
        } else {
            let mut v_val_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3894_);
            v_val_3898_ = leanh::lean_ctor_get(v_fst_3895_, 0);
            leanh::lean_inc(v_val_3898_);
            leanh::lean_dec_ref_known(v_fst_3895_, 1);
            return v_val_3898_;
        }
    } else {
        let mut v_vs_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3902_: usize = 0;
        let mut v___x_3903_: usize = 0;
        let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_3899_ = leanh::lean_ctor_get(v_n_3886_, 0);
        v___x_3900_ = leanh::lean_box(0);
        v___x_3901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3901_, 0, v___x_3900_);
        leanh::lean_ctor_set(v___x_3901_, 1, v_b_3887_);
        v_sz_3902_ = lean_array_size(v_vs_3899_);
        v___x_3903_ = 0usize;
        v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3885_, v_vs_3899_, v_sz_3902_, v___x_3903_, v___x_3901_);
        v_fst_3905_ = leanh::lean_ctor_get(v___x_3904_, 0);
        leanh::lean_inc(v_fst_3905_);
        if leanh::lean_obj_tag(v_fst_3905_) == 0 {
            let mut v_snd_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3906_ = leanh::lean_ctor_get(v___x_3904_, 1);
            leanh::lean_inc(v_snd_3906_);
            leanh::lean_dec_ref(v___x_3904_);
            v___x_3907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3907_, 0, v_snd_3906_);
            return v___x_3907_;
        } else {
            let mut v_val_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3904_);
            v_val_3908_ = leanh::lean_ctor_get(v_fst_3905_, 0);
            leanh::lean_inc(v_val_3908_);
            leanh::lean_dec_ref_known(v_fst_3905_, 1);
            return v_val_3908_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(
    mut v_init_3909_: *mut leanh::LeanObject,
    mut v_text_3910_: *mut leanh::LeanObject,
    mut v_as_3911_: *mut leanh::LeanObject,
    mut v_sz_3912_: usize,
    mut v_i_3913_: usize,
    mut v_b_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3916_: u8 = 0;
    let mut v_snd_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_a_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: usize = 0;
    let mut v___x_3932_: usize = 0;
    let mut v_reuseFailAlloc_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = lean_usize_dec_lt(v_i_3913_, v_sz_3912_);
                if v___x_3916_ == 0 {
                    return v_b_3914_;
                } else {
                    v_snd_3917_ = leanh::lean_ctor_get(v_b_3914_, 1);
                    v_isSharedCheck_3935_ = (!leanh::lean_is_exclusive(v_b_3914_)) as u8;
                    if v_isSharedCheck_3935_ == 0 {
                        v_unused_3936_ = leanh::lean_ctor_get(v_b_3914_, 0);
                        leanh::lean_dec(v_unused_3936_);
                        v___x_3919_ = v_b_3914_;
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3917_);
                        leanh::lean_dec(v_b_3914_);
                        v___x_3919_ = leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3921_ = lean_array_uget_borrowed(v_as_3911_, v_i_3913_);
                leanh::lean_inc(v_snd_3917_);
                v___x_3922_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3909_, v_text_3910_, v_a_3921_, v_snd_3917_);
                if leanh::lean_obj_tag(v___x_3922_) == 0 {
                    v___x_3923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                    if v_isShared_3920_ == 0 {
                        leanh::lean_ctor_set(v___x_3919_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3917_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3917_);
                    v_a_3927_ = leanh::lean_ctor_get(v___x_3922_, 0);
                    leanh::lean_inc(v_a_3927_);
                    leanh::lean_dec_ref_known(v___x_3922_, 1);
                    v___x_3928_ = leanh::lean_box(0);
                    if v_isShared_3920_ == 0 {
                        leanh::lean_ctor_set(v___x_3919_, 1, v_a_3927_);
                        leanh::lean_ctor_set(v___x_3919_, 0, v___x_3928_);
                        v___x_3930_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_a_3927_);
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
    mut v_init_3937_: *mut leanh::LeanObject,
    mut v_text_3938_: *mut leanh::LeanObject,
    mut v_as_3939_: *mut leanh::LeanObject,
    mut v_sz_3940_: *mut leanh::LeanObject,
    mut v_i_3941_: *mut leanh::LeanObject,
    mut v_b_3942_: *mut leanh::LeanObject,
    mut v___y_3943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3944_: usize = 0;
    let mut v_i_boxed_3945_: usize = 0;
    let mut v_res_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3944_ = leanh::lean_unbox_usize(v_sz_3940_);
    leanh::lean_dec(v_sz_3940_);
    v_i_boxed_3945_ = leanh::lean_unbox_usize(v_i_3941_);
    leanh::lean_dec(v_i_3941_);
    v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3937_, v_text_3938_, v_as_3939_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3942_);
    leanh::lean_dec_ref(v_as_3939_);
    leanh::lean_dec_ref(v_text_3938_);
    leanh::lean_dec_ref(v_init_3937_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(
    mut v_init_3947_: *mut leanh::LeanObject,
    mut v_text_3948_: *mut leanh::LeanObject,
    mut v_n_3949_: *mut leanh::LeanObject,
    mut v_b_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3947_, v_text_3948_, v_n_3949_, v_b_3950_);
    leanh::lean_dec_ref(v_n_3949_);
    leanh::lean_dec_ref(v_text_3948_);
    leanh::lean_dec_ref(v_init_3947_);
    return v_res_3952_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(
    mut v_text_3953_: *mut leanh::LeanObject,
    mut v_t_3954_: *mut leanh::LeanObject,
    mut v_init_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_3957_ = leanh::lean_ctor_get(v_t_3954_, 0);
    v_tail_3958_ = leanh::lean_ctor_get(v_t_3954_, 1);
    leanh::lean_inc_ref(v_init_3955_);
    v___x_3959_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3955_, v_text_3953_, v_root_3957_, v_init_3955_);
    leanh::lean_dec_ref(v_init_3955_);
    if leanh::lean_obj_tag(v___x_3959_) == 0 {
        let mut v_a_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3960_ = leanh::lean_ctor_get(v___x_3959_, 0);
        leanh::lean_inc(v_a_3960_);
        leanh::lean_dec_ref_known(v___x_3959_, 1);
        return v_a_3960_;
    } else {
        let mut v_a_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3964_: usize = 0;
        let mut v___x_3965_: usize = 0;
        let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3961_ = leanh::lean_ctor_get(v___x_3959_, 0);
        leanh::lean_inc(v_a_3961_);
        leanh::lean_dec_ref_known(v___x_3959_, 1);
        v___x_3962_ = leanh::lean_box(0);
        v___x_3963_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3963_, 0, v___x_3962_);
        leanh::lean_ctor_set(v___x_3963_, 1, v_a_3961_);
        v_sz_3964_ = lean_array_size(v_tail_3958_);
        v___x_3965_ = 0usize;
        v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3953_, v_tail_3958_, v_sz_3964_, v___x_3965_, v___x_3963_);
        v_fst_3967_ = leanh::lean_ctor_get(v___x_3966_, 0);
        leanh::lean_inc(v_fst_3967_);
        if leanh::lean_obj_tag(v_fst_3967_) == 0 {
            let mut v_snd_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_3968_ = leanh::lean_ctor_get(v___x_3966_, 1);
            leanh::lean_inc(v_snd_3968_);
            leanh::lean_dec_ref(v___x_3966_);
            return v_snd_3968_;
        } else {
            let mut v_val_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_3966_);
            v_val_3969_ = leanh::lean_ctor_get(v_fst_3967_, 0);
            leanh::lean_inc(v_val_3969_);
            leanh::lean_dec_ref_known(v_fst_3967_, 1);
            return v_val_3969_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(
    mut v_text_3970_: *mut leanh::LeanObject,
    mut v_t_3971_: *mut leanh::LeanObject,
    mut v_init_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_3970_, v_t_3971_, v_init_3972_);
    leanh::lean_dec_ref(v_t_3971_);
    leanh::lean_dec_ref(v_text_3970_);
    return v_res_3974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(
    mut v_sz_3975_: usize,
    mut v_i_3976_: usize,
    mut v_bs_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3978_: u8 = 0;
    let mut v_v_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3978_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
                if v___x_3978_ == 0 {
                    return v_bs_3977_;
                } else {
                    v_v_3979_ = lean_array_uget_borrowed(v_bs_3977_, v_i_3976_);
                    v_diagnostics_3980_ = leanh::lean_ctor_get(v_v_3979_, 1);
                    v_msgLog_3981_ = leanh::lean_ctor_get(v_diagnostics_3980_, 0);
                    leanh::lean_inc_ref(v_msgLog_3981_);
                    v___x_3982_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_3988_: *mut leanh::LeanObject,
    mut v_i_3989_: *mut leanh::LeanObject,
    mut v_bs_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3991_: usize = 0;
    let mut v_i_boxed_3992_: usize = 0;
    let mut v_res_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3991_ = leanh::lean_unbox_usize(v_sz_3988_);
    leanh::lean_dec(v_sz_3988_);
    v_i_boxed_3992_ = leanh::lean_unbox_usize(v_i_3989_);
    leanh::lean_dec(v_i_3989_);
    v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_boxed_3991_, v_i_boxed_3992_, v_bs_3990_);
    return v_res_3993_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3995_ = leanh::lean_unsigned_to_nat(32);
    v___x_3996_ = lean_mk_empty_array_with_capacity(v___x_3995_);
    v___x_3997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3997_, 0, v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3998_: usize = 0;
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = 5usize;
    v___x_3999_ = leanh::lean_unsigned_to_nat(0);
    v___x_4000_ = leanh::lean_unsigned_to_nat(32);
    v___x_4001_ = lean_mk_empty_array_with_capacity(v___x_4000_);
    v___x_4002_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1,
    );
    v___x_4003_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4002_);
    leanh::lean_ctor_set(v___x_4003_, 1, v___x_4001_);
    leanh::lean_ctor_set(v___x_4003_, 2, v___x_3999_);
    leanh::lean_ctor_set(v___x_4003_, 3, v___x_3999_);
    leanh::lean_ctor_set_usize(v___x_4003_, 4, v___x_3998_);
    return v___x_4003_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4004_ = l_Lean_NameSet_empty;
    v___x_4005_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2,
    );
    v___x_4006_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4006_, 0, v___x_4005_);
    leanh::lean_ctor_set(v___x_4006_, 1, v___x_4005_);
    leanh::lean_ctor_set(v___x_4006_, 2, v___x_4004_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(
    mut v_doc_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_meta_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSnap_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ranges_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snaps_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4050_: usize = 0;
    let mut v___x_4051_: usize = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: usize = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v_processedSnap_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_unused_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4011_ = leanh::lean_ctor_get(v_doc_4009_, 0);
                v_isSharedCheck_4076_ = (!leanh::lean_is_exclusive(v_doc_4009_)) as u8;
                if v_isSharedCheck_4076_ == 0 {
                    v_unused_4077_ = leanh::lean_ctor_get(v_doc_4009_, 1);
                    leanh::lean_dec(v_unused_4077_);
                    v___x_4013_ = v_doc_4009_;
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toEditableDocumentCore_4011_);
                    leanh::lean_dec(v_doc_4009_);
                    v___x_4013_ = leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4015_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 0);
                leanh::lean_inc_ref(v_meta_4015_);
                v_initSnap_4016_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 1);
                leanh::lean_inc_ref(v_initSnap_4016_);
                v_cmdSnaps_4017_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4011_, 2);
                leanh::lean_inc(v_cmdSnaps_4017_);
                leanh::lean_dec_ref(v_toEditableDocumentCore_4011_);
                v_text_4018_ = leanh::lean_ctor_get(v_meta_4015_, 3);
                leanh::lean_inc_ref(v_text_4018_);
                leanh::lean_dec_ref(v_meta_4015_);
                v_toSnapshot_4030_ = leanh::lean_ctor_get(v_initSnap_4016_, 0);
                leanh::lean_inc_ref(v_toSnapshot_4030_);
                v_metaSnap_4031_ = leanh::lean_ctor_get(v_initSnap_4016_, 1);
                leanh::lean_inc_ref(v_metaSnap_4031_);
                v_result_x3f_4032_ = leanh::lean_ctor_get(v_initSnap_4016_, 4);
                leanh::lean_inc(v_result_x3f_4032_);
                leanh::lean_dec_ref(v_initSnap_4016_);
                v___f_4033_ =
                    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0;
                if leanh::lean_obj_tag(v_result_x3f_4032_) == 0 {
                    v___x_4061_ = leanh::lean_box(0);
                    v___y_4035_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_val_4062_ = leanh::lean_ctor_get(v_result_x3f_4032_, 0);
                    v_isSharedCheck_4075_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_4032_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4064_ = v_result_x3f_4032_;
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4062_);
                        leanh::lean_dec(v_result_x3f_4032_);
                        v___x_4064_ = leanh::lean_box(0);
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_ranges_4021_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                v___x_4022_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_4018_, v_unreported_4020_, v_ranges_4021_);
                leanh::lean_dec_ref(v_unreported_4020_);
                leanh::lean_dec_ref(v_text_4018_);
                v___x_4023_ = l_IO_AsyncList_waitAll___redArg(v_cmdSnaps_4017_);
                v___x_4024_ = lean_task_get_own(v___x_4023_);
                v_fst_4025_ = leanh::lean_ctor_get(v___x_4024_, 0);
                leanh::lean_inc(v_fst_4025_);
                leanh::lean_dec(v___x_4024_);
                v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_fst_4025_, v_fst_4025_, v___x_4022_);
                leanh::lean_dec(v_fst_4025_);
                return v___x_4026_;
            }
            3 => {
                v_unreported_4029_ = leanh::lean_ctor_get(v___y_4028_, 1);
                leanh::lean_inc_ref(v_unreported_4029_);
                leanh::lean_dec_ref(v___y_4028_);
                v_unreported_4020_ = v_unreported_4029_;
                state = 2;
                continue;
            }
            4 => {
                v_stx_x3f_4036_ = leanh::lean_ctor_get(v_metaSnap_4031_, 0);
                leanh::lean_inc(v_stx_x3f_4036_);
                v_reportingRange_4037_ = leanh::lean_ctor_get(v_metaSnap_4031_, 1);
                leanh::lean_inc(v_reportingRange_4037_);
                v___x_4038_ = 1;
                v___x_4039_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_4031_,
                    v___f_4033_,
                    v_stx_x3f_4036_,
                    v_reportingRange_4037_,
                    v___x_4038_,
                );
                v___x_4040_ = leanh::lean_unsigned_to_nat(1);
                v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_4040_);
                v___x_4042_ = lean_array_push(v___x_4041_, v___x_4039_);
                v___x_4043_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_4035_, v___x_4042_);
                if v_isShared_4014_ == 0 {
                    leanh::lean_ctor_set(v___x_4013_, 1, v___x_4043_);
                    leanh::lean_ctor_set(v___x_4013_, 0, v_toSnapshot_4030_);
                    v___x_4045_ = v___x_4013_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_toSnapshot_4030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4043_);
                    v___x_4045_ = v_reuseFailAlloc_4060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_snaps_4046_ = l_Lean_Language_SnapshotTree_getAll(v___x_4045_);
                v___x_4047_ = leanh::lean_unsigned_to_nat(0);
                v___x_4048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
                v___x_4049_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3);
                v_sz_4050_ = lean_array_size(v_snaps_4046_);
                v___x_4051_ = 0usize;
                v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_4050_, v___x_4051_, v_snaps_4046_);
                v___x_4053_ = lean_array_get_size(v___x_4052_);
                v___x_4054_ = lean_nat_dec_lt(v___x_4047_, v___x_4053_);
                if v___x_4054_ == 0 {
                    leanh::lean_dec_ref(v___x_4052_);
                    v_unreported_4020_ = v___x_4048_;
                    state = 2;
                    continue;
                } else {
                    v___x_4055_ = lean_nat_dec_le(v___x_4053_, v___x_4053_);
                    if v___x_4055_ == 0 {
                        if v___x_4054_ == 0 {
                            leanh::lean_dec_ref(v___x_4052_);
                            v_unreported_4020_ = v___x_4048_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4056_ = lean_usize_of_nat(v___x_4053_);
                            v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4056_, v___x_4049_);
                            leanh::lean_dec_ref(v___x_4052_);
                            v___y_4028_ = v___x_4057_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4058_ = lean_usize_of_nat(v___x_4053_);
                        v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4058_, v___x_4049_);
                        leanh::lean_dec_ref(v___x_4052_);
                        v___y_4028_ = v___x_4059_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                v_processedSnap_4066_ = leanh::lean_ctor_get(v_val_4062_, 1);
                leanh::lean_inc_ref(v_processedSnap_4066_);
                leanh::lean_dec(v_val_4062_);
                v_stx_x3f_4067_ = leanh::lean_ctor_get(v_processedSnap_4066_, 0);
                leanh::lean_inc(v_stx_x3f_4067_);
                v_reportingRange_4068_ = leanh::lean_ctor_get(v_processedSnap_4066_, 1);
                leanh::lean_inc(v_reportingRange_4068_);
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
                    leanh::lean_ctor_set(v___x_4064_, 0, v___x_4071_);
                    v___x_4073_ = v___x_4064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
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
    mut v_doc_4078_: *mut leanh::LeanObject,
    mut v_a_4079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(v_doc_4078_);
    return v_res_4080_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(
    mut v_as_4081_: *mut leanh::LeanObject,
    mut v_as_x27_4082_: *mut leanh::LeanObject,
    mut v_b_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_4081_, v_as_x27_4082_, v_b_4083_);
    return v___x_4086_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(
    mut v_as_4087_: *mut leanh::LeanObject,
    mut v_as_x27_4088_: *mut leanh::LeanObject,
    mut v_b_4089_: *mut leanh::LeanObject,
    mut v_a_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(v_as_4087_, v_as_x27_4088_, v_b_4089_, v_a_4090_);
    leanh::lean_dec(v_as_x27_4088_);
    leanh::lean_dec(v_as_4087_);
    return v_res_4092_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(
    mut v_as_4093_: *mut leanh::LeanObject,
    mut v_as_x27_4094_: *mut leanh::LeanObject,
    mut v_b_4095_: *mut leanh::LeanObject,
    mut v_a_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_4094_, v_b_4095_);
    return v___x_4098_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(
    mut v_as_4099_: *mut leanh::LeanObject,
    mut v_as_x27_4100_: *mut leanh::LeanObject,
    mut v_b_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v___y_4103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4104_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(v_as_4099_, v_as_x27_4100_, v_b_4101_, v_a_4102_);
    leanh::lean_dec(v_as_x27_4100_);
    leanh::lean_dec(v_as_4099_);
    return v_res_4104_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
    mut v_a_4105_: *mut leanh::LeanObject,
    mut v_a_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___y_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4123_: u8 = 0;
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_id_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4105_) == 0 {
                    v___x_4107_ = l_List_reverse___redArg(v_a_4106_);
                    return v___x_4107_;
                } else {
                    v_head_4108_ = leanh::lean_ctor_get(v_a_4105_, 0);
                    v_tail_4109_ = leanh::lean_ctor_get(v_a_4105_, 1);
                    v_isSharedCheck_4138_ = (!leanh::lean_is_exclusive(v_a_4105_)) as u8;
                    if v_isSharedCheck_4138_ == 0 {
                        v___x_4111_ = v_a_4105_;
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4109_);
                        leanh::lean_inc(v_head_4108_);
                        leanh::lean_dec(v_a_4105_);
                        v___x_4111_ = leanh::lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_head_4108_) == 0 {
                    v_ns_4119_ = leanh::lean_ctor_get(v_head_4108_, 0);
                    v_except_4120_ = leanh::lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4128_ = (!leanh::lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4122_ = v_head_4108_;
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_except_4120_);
                        leanh::lean_inc(v_ns_4119_);
                        leanh::lean_dec(v_head_4108_);
                        v___x_4122_ = leanh::lean_box(0);
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_id_4129_ = leanh::lean_ctor_get(v_head_4108_, 0);
                    v_declName_4130_ = leanh::lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4137_ = (!leanh::lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4132_ = v_head_4108_;
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_declName_4130_);
                        leanh::lean_inc(v_id_4129_);
                        leanh::lean_dec(v_head_4108_);
                        v___x_4132_ = leanh::lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4112_ == 0 {
                    leanh::lean_ctor_set(v___x_4111_, 1, v_a_4106_);
                    leanh::lean_ctor_set(v___x_4111_, 0, v___y_4114_);
                    v___x_4116_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___y_4114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_a_4106_);
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
                    leanh::lean_ctor_set(v___x_4122_, 1, v___x_4124_);
                    v___x_4126_ = v___x_4122_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_ns_4119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4124_);
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
                    leanh::lean_ctor_set(v___x_4132_, 1, v_id_4129_);
                    leanh::lean_ctor_set(v___x_4132_, 0, v_declName_4130_);
                    v___x_4135_ = v___x_4132_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_declName_4130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_id_4129_);
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
    mut v_a_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4142_ = leanh::lean_ctor_get(v_a_4141_, 0);
                v_snd_4143_ = leanh::lean_ctor_get(v_a_4141_, 1);
                v_isSharedCheck_4159_ = (!leanh::lean_is_exclusive(v_a_4141_)) as u8;
                if v_isSharedCheck_4159_ == 0 {
                    v___x_4145_ = v_a_4141_;
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4143_);
                    leanh::lean_inc(v_fst_4142_);
                    leanh::lean_dec(v_a_4141_);
                    v___x_4145_ = leanh::lean_box(0);
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4147_ = l_Lean_Name_isAnonymous(v_snd_4143_);
                if v___x_4147_ == 0 {
                    v___x_4148_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    leanh::lean_inc(v_snd_4143_);
                    v___x_4149_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4149_, 0, v_snd_4143_);
                    leanh::lean_ctor_set(v___x_4149_, 1, v___x_4148_);
                    v___x_4150_ = lean_array_push(v_fst_4142_, v___x_4149_);
                    v___x_4151_ = l_Lean_Name_getPrefix(v_snd_4143_);
                    leanh::lean_dec(v_snd_4143_);
                    if v_isShared_4146_ == 0 {
                        leanh::lean_ctor_set(v___x_4145_, 1, v___x_4151_);
                        leanh::lean_ctor_set(v___x_4145_, 0, v___x_4150_);
                        v___x_4153_ = v___x_4145_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4150_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4151_);
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
                        v_reuseFailAlloc_4158_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_fst_4142_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_snd_4143_);
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
    mut v_currentNamespace_4162_: *mut leanh::LeanObject,
    mut v_openDecls_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_openNamespaces_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_openNamespaces_4164_ = l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0;
    v___x_4165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4165_, 0, v_openNamespaces_4164_);
    leanh::lean_ctor_set(v___x_4165_, 1, v_currentNamespace_4162_);
    v___x_4166_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v___x_4165_);
    v_fst_4167_ = leanh::lean_ctor_get(v___x_4166_, 0);
    leanh::lean_inc(v_fst_4167_);
    leanh::lean_dec_ref(v___x_4166_);
    v___x_4168_ = leanh::lean_box(0);
    v___x_4169_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
        v_openDecls_4163_,
        v___x_4168_,
    );
    v___x_4170_ = lean_array_mk(v___x_4169_);
    v___x_4171_ = l_Array_append___redArg(v_fst_4167_, v___x_4170_);
    leanh::lean_dec_ref(v___x_4170_);
    return v___x_4171_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(
    mut v_inst_4172_: *mut leanh::LeanObject,
    mut v_a_4173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v_a_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
    mut v_doc_4175_: *mut leanh::LeanObject,
    mut v_currNamespace_4176_: *mut leanh::LeanObject,
    mut v_openDecls_4177_: *mut leanh::LeanObject,
    mut v_val_4178_: *mut leanh::LeanObject,
    mut v_val_4179_: *mut leanh::LeanObject,
    mut v___x_4180_: u8,
    mut v_decl_4181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v_meta_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v_text_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minimizedId_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_unused_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4206_: u8 = 0;
    let mut v_unused_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4182_ = leanh::lean_ctor_get(v_doc_4175_, 0);
                v_isSharedCheck_4206_ = (!leanh::lean_is_exclusive(v_doc_4175_)) as u8;
                if v_isSharedCheck_4206_ == 0 {
                    v_unused_4207_ = leanh::lean_ctor_get(v_doc_4175_, 1);
                    leanh::lean_dec(v_unused_4207_);
                    v___x_4184_ = v_doc_4175_;
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toEditableDocumentCore_4182_);
                    leanh::lean_dec(v_doc_4175_);
                    v___x_4184_ = leanh::lean_box(0);
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4186_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 0);
                v_isSharedCheck_4202_ =
                    (!leanh::lean_is_exclusive(v_toEditableDocumentCore_4182_)) as u8;
                if v_isSharedCheck_4202_ == 0 {
                    v_unused_4203_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 3);
                    leanh::lean_dec(v_unused_4203_);
                    v_unused_4204_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 2);
                    leanh::lean_dec(v_unused_4204_);
                    v_unused_4205_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4182_, 1);
                    leanh::lean_dec(v_unused_4205_);
                    v___x_4188_ = v_toEditableDocumentCore_4182_;
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_meta_4186_);
                    leanh::lean_dec(v_toEditableDocumentCore_4182_);
                    v___x_4188_ = leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4190_ = leanh::lean_ctor_get(v_meta_4186_, 3);
                leanh::lean_inc_ref(v_text_4190_);
                leanh::lean_dec_ref(v_meta_4186_);
                v_minimizedId_4191_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(
                    v_currNamespace_4176_,
                    v_openDecls_4177_,
                    v_decl_4181_,
                );
                if v_isShared_4185_ == 0 {
                    leanh::lean_ctor_set(v___x_4184_, 1, v_val_4179_);
                    leanh::lean_ctor_set(v___x_4184_, 0, v_val_4178_);
                    v___x_4193_ = v___x_4184_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 1, v_val_4179_);
                    v___x_4193_ = v_reuseFailAlloc_4201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4194_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4190_, v___x_4193_);
                leanh::lean_inc(v_minimizedId_4191_);
                v___x_4195_ = l_Lean_Name_toString(v_minimizedId_4191_, v___x_4180_);
                v___x_4196_ = leanh::lean_box(0);
                if v_isShared_4189_ == 0 {
                    leanh::lean_ctor_set(v___x_4188_, 3, v___x_4196_);
                    leanh::lean_ctor_set(v___x_4188_, 2, v___x_4196_);
                    leanh::lean_ctor_set(v___x_4188_, 1, v___x_4195_);
                    leanh::lean_ctor_set(v___x_4188_, 0, v___x_4194_);
                    v___x_4198_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 2, v___x_4196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 3, v___x_4196_);
                    v___x_4198_ = v_reuseFailAlloc_4200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4199_, 0, v_minimizedId_4191_);
                leanh::lean_ctor_set(v___x_4199_, 1, v___x_4198_);
                return v___x_4199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(
    mut v_doc_4208_: *mut leanh::LeanObject,
    mut v_currNamespace_4209_: *mut leanh::LeanObject,
    mut v_openDecls_4210_: *mut leanh::LeanObject,
    mut v_val_4211_: *mut leanh::LeanObject,
    mut v_val_4212_: *mut leanh::LeanObject,
    mut v___x_4213_: *mut leanh::LeanObject,
    mut v_decl_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_172__boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_172__boxed_4215_ = (leanh::lean_unbox(v___x_4213_) as u8);
    v_res_4216_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
        v_doc_4208_,
        v_currNamespace_4209_,
        v_openDecls_4210_,
        v_val_4211_,
        v_val_4212_,
        v___x_172__boxed_4215_,
        v_decl_4214_,
    );
    leanh::lean_dec(v_openDecls_4210_);
    return v_res_4216_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f(
    mut v_doc_4217_: *mut leanh::LeanObject,
    mut v_ctx_4218_: *mut leanh::LeanObject,
    mut v_stx_4219_: *mut leanh::LeanObject,
    mut v_id_4220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v_currNamespace_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = 1;
                v___x_4222_ = l_Lean_Syntax_getPos_x3f(v_stx_4219_, v___x_4221_);
                if leanh::lean_obj_tag(v___x_4222_) == 1 {
                    v_val_4223_ = leanh::lean_ctor_get(v___x_4222_, 0);
                    leanh::lean_inc(v_val_4223_);
                    leanh::lean_dec_ref_known(v___x_4222_, 1);
                    v___x_4224_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4219_, v___x_4221_);
                    if leanh::lean_obj_tag(v___x_4224_) == 1 {
                        v_toCommandContextInfo_4225_ = leanh::lean_ctor_get(v_ctx_4218_, 0);
                        v_val_4226_ = leanh::lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4241_ =
                            (!leanh::lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4241_ == 0 {
                            v___x_4228_ = v___x_4224_;
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4226_);
                            leanh::lean_dec(v___x_4224_);
                            v___x_4228_ = leanh::lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4224_);
                        leanh::lean_dec(v_val_4223_);
                        leanh::lean_dec(v_id_4220_);
                        leanh::lean_dec_ref(v_ctx_4218_);
                        leanh::lean_dec_ref(v_doc_4217_);
                        v___x_4242_ = leanh::lean_box(0);
                        return v___x_4242_;
                    }
                } else {
                    leanh::lean_dec(v___x_4222_);
                    leanh::lean_dec(v_id_4220_);
                    leanh::lean_dec_ref(v_ctx_4218_);
                    leanh::lean_dec_ref(v_doc_4217_);
                    v___x_4243_ = leanh::lean_box(0);
                    return v___x_4243_;
                }
            }
            1 => {
                v_currNamespace_4230_ =
                    leanh::lean_ctor_get(v_toCommandContextInfo_4225_, 5);
                v_openDecls_4231_ = leanh::lean_ctor_get(v_toCommandContextInfo_4225_, 6);
                v___x_4232_ = l_Lean_Name_toString(v_id_4220_, v___x_4221_);
                v___x_4233_ = leanh::lean_box((v___x_4221_) as usize);
                leanh::lean_inc_n(v_openDecls_4231_, 2);
                leanh::lean_inc_n(v_currNamespace_4230_, 2);
                v___f_4234_ = leanh::lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_4234_, 0, v_doc_4217_);
                leanh::lean_closure_set(v___f_4234_, 1, v_currNamespace_4230_);
                leanh::lean_closure_set(v___f_4234_, 2, v_openDecls_4231_);
                leanh::lean_closure_set(v___f_4234_, 3, v_val_4223_);
                leanh::lean_closure_set(v___f_4234_, 4, v_val_4226_);
                leanh::lean_closure_set(v___f_4234_, 5, v___x_4233_);
                v___x_4235_ = l_Lean_Server_FileWorker_collectOpenNamespaces(
                    v_currNamespace_4230_,
                    v_openDecls_4231_,
                );
                v___x_4236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4236_, 0, v___x_4232_);
                leanh::lean_ctor_set(v___x_4236_, 1, v___x_4235_);
                v___x_4237_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                leanh::lean_ctor_set(v___x_4237_, 1, v_ctx_4218_);
                leanh::lean_ctor_set(v___x_4237_, 2, v___f_4234_);
                if v_isShared_4229_ == 0 {
                    leanh::lean_ctor_set(v___x_4228_, 0, v___x_4237_);
                    v___x_4239_ = v___x_4228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
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
    mut v_doc_4244_: *mut leanh::LeanObject,
    mut v_ctx_4245_: *mut leanh::LeanObject,
    mut v_stx_4246_: *mut leanh::LeanObject,
    mut v_id_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(
        v_doc_4244_,
        v_ctx_4245_,
        v_stx_4246_,
        v_id_4247_,
    );
    leanh::lean_dec(v_stx_4246_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(
    mut v_e_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4252_ = l_Lean_Expr_hasMVar(v_e_4249_);
                if v___x_4252_ == 0 {
                    v___x_4253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4253_, 0, v_e_4249_);
                    return v___x_4253_;
                } else {
                    v___x_4254_ = lean_st_ref_get(v___y_4250_);
                    v_mctx_4255_ = leanh::lean_ctor_get(v___x_4254_, 0);
                    leanh::lean_inc_ref(v_mctx_4255_);
                    leanh::lean_dec(v___x_4254_);
                    v___x_4256_ = l_Lean_instantiateMVarsCore(v_mctx_4255_, v_e_4249_);
                    v_fst_4257_ = leanh::lean_ctor_get(v___x_4256_, 0);
                    leanh::lean_inc(v_fst_4257_);
                    v_snd_4258_ = leanh::lean_ctor_get(v___x_4256_, 1);
                    leanh::lean_inc(v_snd_4258_);
                    leanh::lean_dec_ref(v___x_4256_);
                    v___x_4259_ = lean_st_ref_take(v___y_4250_);
                    v_cache_4260_ = leanh::lean_ctor_get(v___x_4259_, 1);
                    v_zetaDeltaFVarIds_4261_ = leanh::lean_ctor_get(v___x_4259_, 2);
                    v_postponed_4262_ = leanh::lean_ctor_get(v___x_4259_, 3);
                    v_diag_4263_ = leanh::lean_ctor_get(v___x_4259_, 4);
                    v_isSharedCheck_4272_ = (!leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4272_ == 0 {
                        v_unused_4273_ = leanh::lean_ctor_get(v___x_4259_, 0);
                        leanh::lean_dec(v_unused_4273_);
                        v___x_4265_ = v___x_4259_;
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_4263_);
                        leanh::lean_inc(v_postponed_4262_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_4261_);
                        leanh::lean_inc(v_cache_4260_);
                        leanh::lean_dec(v___x_4259_);
                        v___x_4265_ = leanh::lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4266_ == 0 {
                    leanh::lean_ctor_set(v___x_4265_, 0, v_snd_4258_);
                    v___x_4268_ = v___x_4265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_snd_4258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_cache_4260_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4271_,
                        2,
                        v_zetaDeltaFVarIds_4261_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_postponed_4262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_diag_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4269_ = lean_st_ref_set(v___y_4250_, v___x_4268_);
                v___x_4270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4270_, 0, v_fst_4257_);
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(
    mut v_e_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4274_, v___y_4275_);
    leanh::lean_dec(v___y_4275_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
    mut v_e_4278_: *mut leanh::LeanObject,
    mut v___y_4279_: *mut leanh::LeanObject,
    mut v___y_4280_: *mut leanh::LeanObject,
    mut v___y_4281_: *mut leanh::LeanObject,
    mut v___y_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4278_, v___y_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(
    mut v_e_4285_: *mut leanh::LeanObject,
    mut v___y_4286_: *mut leanh::LeanObject,
    mut v___y_4287_: *mut leanh::LeanObject,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ =
        l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
            v_e_4285_,
            v___y_4286_,
            v___y_4287_,
            v___y_4288_,
            v___y_4289_,
        );
    leanh::lean_dec(v___y_4289_);
    leanh::lean_dec_ref(v___y_4288_);
    leanh::lean_dec(v___y_4287_);
    leanh::lean_dec_ref(v___y_4286_);
    return v_res_4291_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(
    mut v_expr_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
    mut v___y_4294_: *mut leanh::LeanObject,
    mut v___y_4295_: *mut leanh::LeanObject,
    mut v___y_4296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: u8 = 0;
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v_a_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4296_);
                leanh::lean_inc_ref(v___y_4295_);
                leanh::lean_inc(v___y_4294_);
                leanh::lean_inc_ref(v___y_4293_);
                v___x_4308_ = lean_infer_type(
                    v_expr_4292_,
                    v___y_4293_,
                    v___y_4294_,
                    v___y_4295_,
                    v___y_4296_,
                );
                if leanh::lean_obj_tag(v___x_4308_) == 0 {
                    v_a_4309_ = leanh::lean_ctor_get(v___x_4308_, 0);
                    leanh::lean_inc(v_a_4309_);
                    leanh::lean_dec_ref_known(v___x_4308_, 1);
                    v___x_4310_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_4309_, v___y_4294_);
                    v_a_4311_ = leanh::lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4328_ = (!leanh::lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4313_ = v___x_4310_;
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4311_);
                        leanh::lean_dec(v___x_4310_);
                        v___x_4313_ = leanh::lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_4296_);
                    leanh::lean_dec_ref(v___y_4295_);
                    leanh::lean_dec(v___y_4294_);
                    leanh::lean_dec_ref(v___y_4293_);
                    v_a_4329_ = leanh::lean_ctor_get(v___x_4308_, 0);
                    leanh::lean_inc(v_a_4329_);
                    leanh::lean_dec_ref_known(v___x_4308_, 1);
                    v_a_4305_ = v_a_4329_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_4300_ == 0 {
                    leanh::lean_dec_ref(v___y_4299_);
                    v___x_4301_ = leanh::lean_box(0);
                    v___x_4302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
                    return v___x_4302_;
                } else {
                    v___x_4303_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4303_, 0, v___y_4299_);
                    return v___x_4303_;
                }
            }
            2 => {
                v___x_4306_ = l_Lean_Exception_isInterrupt(v_a_4305_);
                if v___x_4306_ == 0 {
                    leanh::lean_inc_ref(v_a_4305_);
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
                leanh::lean_dec(v___y_4296_);
                leanh::lean_dec_ref(v___y_4295_);
                leanh::lean_dec(v___y_4294_);
                leanh::lean_dec_ref(v___y_4293_);
                if leanh::lean_obj_tag(v___x_4315_) == 0 {
                    v_a_4316_ = leanh::lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4326_ = (!leanh::lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4318_ = v___x_4315_;
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4316_);
                        leanh::lean_dec(v___x_4315_);
                        v___x_4318_ = leanh::lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4313_);
                    v_a_4327_ = leanh::lean_ctor_get(v___x_4315_, 0);
                    leanh::lean_inc(v_a_4327_);
                    leanh::lean_dec_ref_known(v___x_4315_, 1);
                    v_a_4305_ = v_a_4327_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_4314_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4313_, 1);
                    leanh::lean_ctor_set(v___x_4313_, 0, v_a_4316_);
                    v___x_4321_ = v___x_4313_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4319_ == 0 {
                    leanh::lean_ctor_set(v___x_4318_, 0, v___x_4321_);
                    v___x_4323_ = v___x_4318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
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
    mut v_expr_4330_: *mut leanh::LeanObject,
    mut v___y_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
    mut v___y_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_val_4337_: *mut leanh::LeanObject,
    mut v_val_4338_: *mut leanh::LeanObject,
    mut v_text_4339_: *mut leanh::LeanObject,
    mut v_decl_4340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4341_, 0, v_val_4337_);
    leanh::lean_ctor_set(v___x_4341_, 1, v_val_4338_);
    v___x_4342_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4339_, v___x_4341_);
    v___x_4343_ = l_Lean_Name_getString_x21(v_decl_4340_);
    v___x_4344_ = leanh::lean_box(0);
    v___x_4345_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4345_, 0, v___x_4342_);
    leanh::lean_ctor_set(v___x_4345_, 1, v___x_4343_);
    leanh::lean_ctor_set(v___x_4345_, 2, v___x_4344_);
    leanh::lean_ctor_set(v___x_4345_, 3, v___x_4344_);
    v___x_4346_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4346_, 0, v_decl_4340_);
    leanh::lean_ctor_set(v___x_4346_, 1, v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(
    mut v_sz_4347_: usize,
    mut v_i_4348_: usize,
    mut v_bs_4349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4350_: u8 = 0;
    let mut v_v_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: usize = 0;
    let mut v___x_4357_: usize = 0;
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4350_ = lean_usize_dec_lt(v_i_4348_, v_sz_4347_);
                if v___x_4350_ == 0 {
                    return v_bs_4349_;
                } else {
                    v_v_4351_ = lean_array_uget(v_bs_4349_, v_i_4348_);
                    v___x_4352_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4353_ = lean_array_uset(v_bs_4349_, v_i_4348_, v___x_4352_);
                    v___x_4354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    v___x_4355_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4355_, 0, v_v_4351_);
                    leanh::lean_ctor_set(v___x_4355_, 1, v___x_4354_);
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
    mut v_sz_4360_: *mut leanh::LeanObject,
    mut v_i_4361_: *mut leanh::LeanObject,
    mut v_bs_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4363_: usize = 0;
    let mut v_i_boxed_4364_: usize = 0;
    let mut v_res_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4363_ = leanh::lean_unbox_usize(v_sz_4360_);
    leanh::lean_dec(v_sz_4360_);
    v_i_boxed_4364_ = leanh::lean_unbox_usize(v_i_4361_);
    leanh::lean_dec(v_i_4361_);
    v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_4363_, v_i_boxed_4364_, v_bs_4362_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f(
    mut v_doc_4366_: *mut leanh::LeanObject,
    mut v_ctx_4367_: *mut leanh::LeanObject,
    mut v_ti_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toElabInfo_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v_val_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v_toEditableDocumentCore_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_meta_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4404_: usize = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_unused_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toElabInfo_4370_ = leanh::lean_ctor_get(v_ti_4368_, 0);
                leanh::lean_inc_ref(v_toElabInfo_4370_);
                v_lctx_4371_ = leanh::lean_ctor_get(v_ti_4368_, 1);
                leanh::lean_inc_ref(v_lctx_4371_);
                v_expr_4372_ = leanh::lean_ctor_get(v_ti_4368_, 3);
                leanh::lean_inc_ref(v_expr_4372_);
                leanh::lean_dec_ref(v_ti_4368_);
                v_stx_4373_ = leanh::lean_ctor_get(v_toElabInfo_4370_, 1);
                leanh::lean_inc(v_stx_4373_);
                leanh::lean_dec_ref(v_toElabInfo_4370_);
                v___x_4374_ = 1;
                v___x_4375_ = l_Lean_Syntax_getPos_x3f(v_stx_4373_, v___x_4374_);
                if leanh::lean_obj_tag(v___x_4375_) == 1 {
                    v_val_4376_ = leanh::lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4441_ = (!leanh::lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4441_ == 0 {
                        v___x_4378_ = v___x_4375_;
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4376_);
                        leanh::lean_dec(v___x_4375_);
                        v___x_4378_ = leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4375_);
                    leanh::lean_dec(v_stx_4373_);
                    leanh::lean_dec_ref(v_expr_4372_);
                    leanh::lean_dec_ref(v_lctx_4371_);
                    leanh::lean_dec_ref(v_ctx_4367_);
                    leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4442_ = leanh::lean_box(0);
                    v___x_4443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4443_, 0, v___x_4442_);
                    return v___x_4443_;
                }
            }
            1 => {
                v___x_4380_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4373_, v___x_4374_);
                leanh::lean_dec(v_stx_4373_);
                if leanh::lean_obj_tag(v___x_4380_) == 1 {
                    leanh::lean_del_object(v___x_4378_);
                    v_val_4381_ = leanh::lean_ctor_get(v___x_4380_, 0);
                    leanh::lean_inc(v_val_4381_);
                    leanh::lean_dec_ref_known(v___x_4380_, 1);
                    v___f_4382_ = leanh::lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___f_4382_, 0, v_expr_4372_);
                    leanh::lean_inc_ref(v_ctx_4367_);
                    v___x_4383_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_4367_,
                        v_lctx_4371_,
                        v___f_4382_,
                    );
                    if leanh::lean_obj_tag(v___x_4383_) == 0 {
                        v_a_4384_ = leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4428_ =
                            (!leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4386_ = v___x_4383_;
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4384_);
                            leanh::lean_dec(v___x_4383_);
                            v___x_4386_ = leanh::lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4381_);
                        leanh::lean_dec(v_val_4376_);
                        leanh::lean_dec_ref(v_ctx_4367_);
                        leanh::lean_dec_ref(v_doc_4366_);
                        v_a_4429_ = leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4436_ =
                            (!leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4436_ == 0 {
                            v___x_4431_ = v___x_4383_;
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4429_);
                            leanh::lean_dec(v___x_4383_);
                            v___x_4431_ = leanh::lean_box(0);
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4380_);
                    leanh::lean_dec(v_val_4376_);
                    leanh::lean_dec_ref(v_expr_4372_);
                    leanh::lean_dec_ref(v_lctx_4371_);
                    leanh::lean_dec_ref(v_ctx_4367_);
                    leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4437_ = leanh::lean_box(0);
                    if v_isShared_4379_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4378_, 0);
                        leanh::lean_ctor_set(v___x_4378_, 0, v___x_4437_);
                        v___x_4439_ = v___x_4378_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
                        v___x_4439_ = v_reuseFailAlloc_4440_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4384_) == 1 {
                    v_val_4388_ = leanh::lean_ctor_get(v_a_4384_, 0);
                    v_isSharedCheck_4423_ = (!leanh::lean_is_exclusive(v_a_4384_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4390_ = v_a_4384_;
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4388_);
                        leanh::lean_dec(v_a_4384_);
                        v___x_4390_ = leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4384_);
                    leanh::lean_dec(v_val_4381_);
                    leanh::lean_dec(v_val_4376_);
                    leanh::lean_dec_ref(v_ctx_4367_);
                    leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4424_ = leanh::lean_box(0);
                    if v_isShared_4387_ == 0 {
                        leanh::lean_ctor_set(v___x_4386_, 0, v___x_4424_);
                        v___x_4426_ = v___x_4386_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
                        v___x_4426_ = v_reuseFailAlloc_4427_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4392_ = lean_array_get_size(v_val_4388_);
                v___x_4393_ = leanh::lean_unsigned_to_nat(0);
                v___x_4394_ = lean_nat_dec_eq(v___x_4392_, v___x_4393_);
                if v___x_4394_ == 0 {
                    v_toEditableDocumentCore_4395_ = leanh::lean_ctor_get(v_doc_4366_, 0);
                    v_isSharedCheck_4417_ = (!leanh::lean_is_exclusive(v_doc_4366_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v_unused_4418_ = leanh::lean_ctor_get(v_doc_4366_, 1);
                        leanh::lean_dec(v_unused_4418_);
                        v___x_4397_ = v_doc_4366_;
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_toEditableDocumentCore_4395_);
                        leanh::lean_dec(v_doc_4366_);
                        v___x_4397_ = leanh::lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4390_);
                    leanh::lean_dec(v_val_4388_);
                    leanh::lean_dec(v_val_4381_);
                    leanh::lean_dec(v_val_4376_);
                    leanh::lean_dec_ref(v_ctx_4367_);
                    leanh::lean_dec_ref(v_doc_4366_);
                    v___x_4419_ = leanh::lean_box(0);
                    if v_isShared_4387_ == 0 {
                        leanh::lean_ctor_set(v___x_4386_, 0, v___x_4419_);
                        v___x_4421_ = v___x_4386_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_meta_4399_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4395_, 0);
                leanh::lean_inc_ref(v_meta_4399_);
                leanh::lean_dec_ref(v_toEditableDocumentCore_4395_);
                v_text_4400_ = leanh::lean_ctor_get(v_meta_4399_, 3);
                leanh::lean_inc_ref(v_text_4400_);
                leanh::lean_dec_ref(v_meta_4399_);
                v_source_4401_ = leanh::lean_ctor_get(v_text_4400_, 0);
                leanh::lean_inc_ref(v_source_4401_);
                leanh::lean_inc(v_val_4381_);
                leanh::lean_inc(v_val_4376_);
                v___f_4402_ = leanh::lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_4402_, 0, v_val_4376_);
                leanh::lean_closure_set(v___f_4402_, 1, v_val_4381_);
                leanh::lean_closure_set(v___f_4402_, 2, v_text_4400_);
                v___x_4403_ = lean_string_utf8_extract(v_source_4401_, v_val_4376_, v_val_4381_);
                leanh::lean_dec(v_val_4381_);
                leanh::lean_dec(v_val_4376_);
                leanh::lean_dec_ref(v_source_4401_);
                v_sz_4404_ = lean_array_size(v_val_4388_);
                v___x_4405_ = 0usize;
                v___x_4406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4404_, v___x_4405_, v_val_4388_);
                if v_isShared_4398_ == 0 {
                    leanh::lean_ctor_set(v___x_4397_, 1, v___x_4406_);
                    leanh::lean_ctor_set(v___x_4397_, 0, v___x_4403_);
                    v___x_4408_ = v___x_4397_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4406_);
                    v___x_4408_ = v_reuseFailAlloc_4416_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4409_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4409_, 0, v___x_4408_);
                leanh::lean_ctor_set(v___x_4409_, 1, v_ctx_4367_);
                leanh::lean_ctor_set(v___x_4409_, 2, v___f_4402_);
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4390_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4415_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4387_ == 0 {
                    leanh::lean_ctor_set(v___x_4386_, 0, v___x_4411_);
                    v___x_4413_ = v___x_4386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
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
                    v_reuseFailAlloc_4435_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
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
    mut v_doc_4444_: *mut leanh::LeanObject,
    mut v_ctx_4445_: *mut leanh::LeanObject,
    mut v_ti_4446_: *mut leanh::LeanObject,
    mut v_a_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4448_ =
        l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_4444_, v_ctx_4445_, v_ti_4446_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(
    mut v_doc_4449_: *mut leanh::LeanObject,
    mut v_val_4450_: *mut leanh::LeanObject,
    mut v_val_4451_: *mut leanh::LeanObject,
    mut v_decl_4452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v_meta_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4460_: u8 = 0;
    let mut v_text_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_unused_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_unused_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4453_ = leanh::lean_ctor_get(v_doc_4449_, 0);
                v_isSharedCheck_4476_ = (!leanh::lean_is_exclusive(v_doc_4449_)) as u8;
                if v_isSharedCheck_4476_ == 0 {
                    v_unused_4477_ = leanh::lean_ctor_get(v_doc_4449_, 1);
                    leanh::lean_dec(v_unused_4477_);
                    v___x_4455_ = v_doc_4449_;
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toEditableDocumentCore_4453_);
                    leanh::lean_dec(v_doc_4449_);
                    v___x_4455_ = leanh::lean_box(0);
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4457_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 0);
                v_isSharedCheck_4472_ =
                    (!leanh::lean_is_exclusive(v_toEditableDocumentCore_4453_)) as u8;
                if v_isSharedCheck_4472_ == 0 {
                    v_unused_4473_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 3);
                    leanh::lean_dec(v_unused_4473_);
                    v_unused_4474_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 2);
                    leanh::lean_dec(v_unused_4474_);
                    v_unused_4475_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4453_, 1);
                    leanh::lean_dec(v_unused_4475_);
                    v___x_4459_ = v_toEditableDocumentCore_4453_;
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_meta_4457_);
                    leanh::lean_dec(v_toEditableDocumentCore_4453_);
                    v___x_4459_ = leanh::lean_box(0);
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4461_ = leanh::lean_ctor_get(v_meta_4457_, 3);
                leanh::lean_inc_ref(v_text_4461_);
                leanh::lean_dec_ref(v_meta_4457_);
                if v_isShared_4456_ == 0 {
                    leanh::lean_ctor_set(v___x_4455_, 1, v_val_4451_);
                    leanh::lean_ctor_set(v___x_4455_, 0, v_val_4450_);
                    v___x_4463_ = v___x_4455_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_val_4450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_val_4451_);
                    v___x_4463_ = v_reuseFailAlloc_4471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4464_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4461_, v___x_4463_);
                v___x_4465_ = l_Lean_Name_getString_x21(v_decl_4452_);
                v___x_4466_ = leanh::lean_box(0);
                if v_isShared_4460_ == 0 {
                    leanh::lean_ctor_set(v___x_4459_, 3, v___x_4466_);
                    leanh::lean_ctor_set(v___x_4459_, 2, v___x_4466_);
                    leanh::lean_ctor_set(v___x_4459_, 1, v___x_4465_);
                    leanh::lean_ctor_set(v___x_4459_, 0, v___x_4464_);
                    v___x_4468_ = v___x_4459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 2, v___x_4466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 3, v___x_4466_);
                    v___x_4468_ = v_reuseFailAlloc_4470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4469_, 0, v_decl_4452_);
                leanh::lean_ctor_set(v___x_4469_, 1, v___x_4468_);
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
    mut v_doc_4478_: *mut leanh::LeanObject,
    mut v_ctx_4479_: *mut leanh::LeanObject,
    mut v_stx_4480_: *mut leanh::LeanObject,
    mut v_id_4481_: *mut leanh::LeanObject,
    mut v_lctx_4482_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: u8 = 0;
    let mut v___f_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_unused_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ = 1;
                v___x_4486_ = l_Lean_Syntax_getPos_x3f(v_stx_4480_, v___x_4485_);
                if leanh::lean_obj_tag(v___x_4486_) == 1 {
                    v_val_4487_ = leanh::lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4546_ = (!leanh::lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4546_ == 0 {
                        v___x_4489_ = v___x_4486_;
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4487_);
                        leanh::lean_dec(v___x_4486_);
                        v___x_4489_ = leanh::lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4486_);
                    leanh::lean_dec(v_expectedType_x3f_4483_);
                    leanh::lean_dec_ref(v_lctx_4482_);
                    leanh::lean_dec(v_id_4481_);
                    leanh::lean_dec_ref(v_ctx_4479_);
                    leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4547_ = leanh::lean_box(0);
                    v___x_4548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4548_, 0, v___x_4547_);
                    return v___x_4548_;
                }
            }
            1 => {
                v___x_4491_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4480_, v___x_4485_);
                if leanh::lean_obj_tag(v___x_4491_) == 1 {
                    leanh::lean_del_object(v___x_4489_);
                    if leanh::lean_obj_tag(v_expectedType_x3f_4483_) == 1 {
                        v_val_4492_ = leanh::lean_ctor_get(v___x_4491_, 0);
                        leanh::lean_inc(v_val_4492_);
                        leanh::lean_dec_ref_known(v___x_4491_, 1);
                        v_val_4493_ = leanh::lean_ctor_get(v_expectedType_x3f_4483_, 0);
                        v_isSharedCheck_4532_ =
                            (!leanh::lean_is_exclusive(v_expectedType_x3f_4483_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4495_ = v_expectedType_x3f_4483_;
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4493_);
                            leanh::lean_dec(v_expectedType_x3f_4483_);
                            v___x_4495_ = leanh::lean_box(0);
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4487_);
                        leanh::lean_dec(v_expectedType_x3f_4483_);
                        leanh::lean_dec_ref(v_lctx_4482_);
                        leanh::lean_dec(v_id_4481_);
                        leanh::lean_dec_ref(v_ctx_4479_);
                        leanh::lean_dec_ref(v_doc_4478_);
                        v_isSharedCheck_4540_ =
                            (!leanh::lean_is_exclusive(v___x_4491_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v_unused_4541_ = leanh::lean_ctor_get(v___x_4491_, 0);
                            leanh::lean_dec(v_unused_4541_);
                            v___x_4534_ = v___x_4491_;
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4491_);
                            v___x_4534_ = leanh::lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4491_);
                    leanh::lean_dec(v_val_4487_);
                    leanh::lean_dec(v_expectedType_x3f_4483_);
                    leanh::lean_dec_ref(v_lctx_4482_);
                    leanh::lean_dec(v_id_4481_);
                    leanh::lean_dec_ref(v_ctx_4479_);
                    leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4542_ = leanh::lean_box(0);
                    if v_isShared_4490_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4489_, 0);
                        leanh::lean_ctor_set(v___x_4489_, 0, v___x_4542_);
                        v___x_4544_ = v___x_4489_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
                        v___x_4544_ = v_reuseFailAlloc_4545_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4497_ = leanh::lean_alloc_closure(
                    l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed
                        as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___x_4497_, 0, v_val_4493_);
                leanh::lean_inc_ref(v_ctx_4479_);
                v___x_4498_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                    v_ctx_4479_,
                    v_lctx_4482_,
                    v___x_4497_,
                );
                if leanh::lean_obj_tag(v___x_4498_) == 0 {
                    v_a_4499_ = leanh::lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4523_ = (!leanh::lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4523_ == 0 {
                        v___x_4501_ = v___x_4498_;
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4499_);
                        leanh::lean_dec(v___x_4498_);
                        v___x_4501_ = leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4495_);
                    leanh::lean_dec(v_val_4492_);
                    leanh::lean_dec(v_val_4487_);
                    leanh::lean_dec(v_id_4481_);
                    leanh::lean_dec_ref(v_ctx_4479_);
                    leanh::lean_dec_ref(v_doc_4478_);
                    v_a_4524_ = leanh::lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4531_ = (!leanh::lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4531_ == 0 {
                        v___x_4526_ = v___x_4498_;
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4524_);
                        leanh::lean_dec(v___x_4498_);
                        v___x_4526_ = leanh::lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4503_ = lean_array_get_size(v_a_4499_);
                v___x_4504_ = leanh::lean_unsigned_to_nat(0);
                v___x_4505_ = lean_nat_dec_eq(v___x_4503_, v___x_4504_);
                if v___x_4505_ == 0 {
                    v___f_4506_ = leanh::lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_4506_, 0, v_doc_4478_);
                    leanh::lean_closure_set(v___f_4506_, 1, v_val_4487_);
                    leanh::lean_closure_set(v___f_4506_, 2, v_val_4492_);
                    v___x_4507_ = l_Lean_Name_toString(v_id_4481_, v___x_4485_);
                    v_sz_4508_ = lean_array_size(v_a_4499_);
                    v___x_4509_ = 0usize;
                    v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4508_, v___x_4509_, v_a_4499_);
                    v___x_4511_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4511_, 0, v___x_4507_);
                    leanh::lean_ctor_set(v___x_4511_, 1, v___x_4510_);
                    v___x_4512_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    leanh::lean_ctor_set(v___x_4512_, 1, v_ctx_4479_);
                    leanh::lean_ctor_set(v___x_4512_, 2, v___f_4506_);
                    if v_isShared_4496_ == 0 {
                        leanh::lean_ctor_set(v___x_4495_, 0, v___x_4512_);
                        v___x_4514_ = v___x_4495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4512_);
                        v___x_4514_ = v_reuseFailAlloc_4518_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4499_);
                    leanh::lean_del_object(v___x_4495_);
                    leanh::lean_dec(v_val_4492_);
                    leanh::lean_dec(v_val_4487_);
                    leanh::lean_dec(v_id_4481_);
                    leanh::lean_dec_ref(v_ctx_4479_);
                    leanh::lean_dec_ref(v_doc_4478_);
                    v___x_4519_ = leanh::lean_box(0);
                    if v_isShared_4502_ == 0 {
                        leanh::lean_ctor_set(v___x_4501_, 0, v___x_4519_);
                        v___x_4521_ = v___x_4501_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
                        v___x_4521_ = v_reuseFailAlloc_4522_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4502_ == 0 {
                    leanh::lean_ctor_set(v___x_4501_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4501_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
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
                    v_reuseFailAlloc_4530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4529_;
            }
            9 => {
                v___x_4536_ = leanh::lean_box(0);
                if v_isShared_4535_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4534_, 0);
                    leanh::lean_ctor_set(v___x_4534_, 0, v___x_4536_);
                    v___x_4538_ = v___x_4534_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
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
    mut v_doc_4549_: *mut leanh::LeanObject,
    mut v_ctx_4550_: *mut leanh::LeanObject,
    mut v_stx_4551_: *mut leanh::LeanObject,
    mut v_id_4552_: *mut leanh::LeanObject,
    mut v_lctx_4553_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_4554_: *mut leanh::LeanObject,
    mut v_a_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4556_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
        v_doc_4549_,
        v_ctx_4550_,
        v_stx_4551_,
        v_id_4552_,
        v_lctx_4553_,
        v_expectedType_x3f_4554_,
    );
    leanh::lean_dec(v_stx_4551_);
    return v_res_4556_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(
    mut v_doc_4557_: *mut leanh::LeanObject,
    mut v_as_4558_: *mut leanh::LeanObject,
    mut v_sz_4559_: usize,
    mut v_i_4560_: usize,
    mut v_b_4561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: usize = 0;
    let mut v_query_x3f_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: u8 = 0;
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_termInfo_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_ctx_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4572_ = lean_usize_dec_lt(v_i_4560_, v_sz_4559_);
                if v___x_4572_ == 0 {
                    leanh::lean_dec_ref(v_doc_4557_);
                    v___x_4573_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4573_, 0, v_b_4561_);
                    return v___x_4573_;
                } else {
                    v_a_4574_ = lean_array_uget_borrowed(v_as_4558_, v_i_4560_);
                    v_fst_4575_ = leanh::lean_ctor_get(v_a_4574_, 0);
                    v_info_4576_ = leanh::lean_ctor_get(v_fst_4575_, 2);
                    match leanh::lean_obj_tag(v_info_4576_) {
                        1 => {
                            v_ctx_4577_ = leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4578_ = leanh::lean_ctor_get(v_info_4576_, 0);
                            v_id_4579_ = leanh::lean_ctor_get(v_info_4576_, 1);
                            leanh::lean_inc(v_id_4579_);
                            leanh::lean_inc_ref(v_ctx_4577_);
                            leanh::lean_inc_ref(v_doc_4557_);
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
                            v_ctx_4581_ = leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_termInfo_4582_ = leanh::lean_ctor_get(v_info_4576_, 0);
                            leanh::lean_inc_ref(v_termInfo_4582_);
                            leanh::lean_inc_ref(v_ctx_4581_);
                            leanh::lean_inc_ref(v_doc_4557_);
                            v___x_4583_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4581_,
                                v_termInfo_4582_,
                            );
                            if leanh::lean_obj_tag(v___x_4583_) == 0 {
                                v_a_4584_ = leanh::lean_ctor_get(v___x_4583_, 0);
                                leanh::lean_inc(v_a_4584_);
                                leanh::lean_dec_ref_known(v___x_4583_, 1);
                                v_query_x3f_4569_ = v_a_4584_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_4561_);
                                leanh::lean_dec_ref(v_doc_4557_);
                                v_a_4585_ = leanh::lean_ctor_get(v___x_4583_, 0);
                                v_isSharedCheck_4593_ =
                                    (!leanh::lean_is_exclusive(v___x_4583_)) as u8;
                                if v_isSharedCheck_4593_ == 0 {
                                    v___x_4587_ = v___x_4583_;
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4585_);
                                    leanh::lean_dec(v___x_4583_);
                                    v___x_4587_ = leanh::lean_box(0);
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        2 => {
                            v_ctx_4594_ = leanh::lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4595_ = leanh::lean_ctor_get(v_info_4576_, 0);
                            v_id_4596_ = leanh::lean_ctor_get(v_info_4576_, 1);
                            v_lctx_4597_ = leanh::lean_ctor_get(v_info_4576_, 2);
                            v_expectedType_x3f_4598_ = leanh::lean_ctor_get(v_info_4576_, 3);
                            leanh::lean_inc(v_expectedType_x3f_4598_);
                            leanh::lean_inc_ref(v_lctx_4597_);
                            leanh::lean_inc(v_id_4596_);
                            leanh::lean_inc_ref(v_ctx_4594_);
                            leanh::lean_inc_ref(v_doc_4557_);
                            v___x_4599_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4594_,
                                v_stx_4595_,
                                v_id_4596_,
                                v_lctx_4597_,
                                v_expectedType_x3f_4598_,
                            );
                            if leanh::lean_obj_tag(v___x_4599_) == 0 {
                                v_a_4600_ = leanh::lean_ctor_get(v___x_4599_, 0);
                                leanh::lean_inc(v_a_4600_);
                                leanh::lean_dec_ref_known(v___x_4599_, 1);
                                v_query_x3f_4569_ = v_a_4600_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_4561_);
                                leanh::lean_dec_ref(v_doc_4557_);
                                v_a_4601_ = leanh::lean_ctor_get(v___x_4599_, 0);
                                v_isSharedCheck_4609_ =
                                    (!leanh::lean_is_exclusive(v___x_4599_)) as u8;
                                if v_isSharedCheck_4609_ == 0 {
                                    v___x_4603_ = v___x_4599_;
                                    v_isShared_4604_ = v_isSharedCheck_4609_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4601_);
                                    leanh::lean_dec(v___x_4599_);
                                    v___x_4603_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_query_x3f_4569_) == 1 {
                    v_val_4570_ = leanh::lean_ctor_get(v_query_x3f_4569_, 0);
                    leanh::lean_inc(v_val_4570_);
                    leanh::lean_dec_ref_known(v_query_x3f_4569_, 1);
                    v___x_4571_ = lean_array_push(v_b_4561_, v_val_4570_);
                    v_a_4564_ = v___x_4571_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_query_x3f_4569_);
                    v_a_4564_ = v_b_4561_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4589_ = l_Lean_Server_RequestError_ofIoError(v_a_4585_);
                if v_isShared_4588_ == 0 {
                    leanh::lean_ctor_set(v___x_4587_, 0, v___x_4589_);
                    v___x_4591_ = v___x_4587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
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
                    leanh::lean_ctor_set(v___x_4603_, 0, v___x_4605_);
                    v___x_4607_ = v___x_4603_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
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
    mut v_doc_4610_: *mut leanh::LeanObject,
    mut v_as_4611_: *mut leanh::LeanObject,
    mut v_sz_4612_: *mut leanh::LeanObject,
    mut v_i_4613_: *mut leanh::LeanObject,
    mut v_b_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4616_: usize = 0;
    let mut v_i_boxed_4617_: usize = 0;
    let mut v_res_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4616_ = leanh::lean_unbox_usize(v_sz_4612_);
    leanh::lean_dec(v_sz_4612_);
    v_i_boxed_4617_ = leanh::lean_unbox_usize(v_i_4613_);
    leanh::lean_dec(v_i_4613_);
    v_res_4618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4610_, v_as_4611_, v_sz_boxed_4616_, v_i_boxed_4617_, v_b_4614_);
    leanh::lean_dec_ref(v_as_4611_);
    return v_res_4618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(
    mut v_doc_4619_: *mut leanh::LeanObject,
    mut v_as_4620_: *mut leanh::LeanObject,
    mut v_sz_4621_: usize,
    mut v_i_4622_: usize,
    mut v_b_4623_: *mut leanh::LeanObject,
    mut v___y_4624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: usize = 0;
    let mut v___x_4637_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4626_ = lean_usize_dec_lt(v_i_4622_, v_sz_4621_);
                if v___x_4626_ == 0 {
                    leanh::lean_dec_ref(v_doc_4619_);
                    v___x_4627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4627_, 0, v_b_4623_);
                    return v___x_4627_;
                } else {
                    v_a_4628_ = lean_array_uget_borrowed(v_as_4620_, v_i_4622_);
                    v_sz_4629_ = lean_array_size(v_a_4628_);
                    v___x_4630_ = 0usize;
                    leanh::lean_inc_ref(v_doc_4619_);
                    v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4619_, v_a_4628_, v_sz_4629_, v___x_4630_, v_b_4623_);
                    if leanh::lean_obj_tag(v___x_4631_) == 0 {
                        v_a_4632_ = leanh::lean_ctor_get(v___x_4631_, 0);
                        leanh::lean_inc(v_a_4632_);
                        v___x_4633_ = lean_array_get_size(v_a_4632_);
                        v___x_4634_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4635_ = lean_nat_dec_eq(v___x_4633_, v___x_4634_);
                        if v___x_4635_ == 0 {
                            leanh::lean_dec(v_a_4632_);
                            leanh::lean_dec_ref(v_doc_4619_);
                            return v___x_4631_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_4631_, 1);
                            v___x_4636_ = 1usize;
                            v___x_4637_ = lean_usize_add(v_i_4622_, v___x_4636_);
                            v_i_4622_ = v___x_4637_;
                            v_b_4623_ = v_a_4632_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_doc_4619_);
                        return v___x_4631_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(
    mut v_doc_4639_: *mut leanh::LeanObject,
    mut v_as_4640_: *mut leanh::LeanObject,
    mut v_sz_4641_: *mut leanh::LeanObject,
    mut v_i_4642_: *mut leanh::LeanObject,
    mut v_b_4643_: *mut leanh::LeanObject,
    mut v___y_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4646_: usize = 0;
    let mut v_i_boxed_4647_: usize = 0;
    let mut v_res_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4646_ = leanh::lean_unbox_usize(v_sz_4641_);
    leanh::lean_dec(v_sz_4641_);
    v_i_boxed_4647_ = leanh::lean_unbox_usize(v_i_4642_);
    leanh::lean_dec(v_i_4642_);
    v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4639_, v_as_4640_, v_sz_boxed_4646_, v_i_boxed_4647_, v_b_4643_, v___y_4644_);
    leanh::lean_dec_ref(v___y_4644_);
    leanh::lean_dec_ref(v_as_4640_);
    return v_res_4648_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries(
    mut v_doc_4651_: *mut leanh::LeanObject,
    mut v_requestedPos_4652_: *mut leanh::LeanObject,
    mut v_a_4653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_4655_ = leanh::lean_ctor_get(v_doc_4651_, 0);
    v___x_4656_ = 1;
    leanh::lean_inc(v_requestedPos_4652_);
    leanh::lean_inc_ref(v_doc_4651_);
    v___x_4657_ =
        l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_4651_, v_requestedPos_4652_, v___x_4656_);
    v___x_4658_ = lean_task_get_own(v___x_4657_);
    if leanh::lean_obj_tag(v___x_4658_) == 1 {
        let mut v_val_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_meta_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_queries_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4667_: usize = 0;
        let mut v___x_4668_: usize = 0;
        let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4659_ = leanh::lean_ctor_get(v___x_4658_, 0);
        leanh::lean_inc(v_val_4659_);
        leanh::lean_dec_ref_known(v___x_4658_, 1);
        v_meta_4660_ = leanh::lean_ctor_get(v_toEditableDocumentCore_4655_, 0);
        v_fst_4661_ = leanh::lean_ctor_get(v_val_4659_, 0);
        leanh::lean_inc(v_fst_4661_);
        v_snd_4662_ = leanh::lean_ctor_get(v_val_4659_, 1);
        leanh::lean_inc(v_snd_4662_);
        leanh::lean_dec(v_val_4659_);
        v_text_4663_ = leanh::lean_ctor_get(v_meta_4660_, 3);
        leanh::lean_inc_ref(v_text_4663_);
        v___x_4664_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
            v_text_4663_,
            v_requestedPos_4652_,
            v_fst_4661_,
            v_snd_4662_,
        );
        v_fst_4665_ = leanh::lean_ctor_get(v___x_4664_, 0);
        leanh::lean_inc(v_fst_4665_);
        leanh::lean_dec_ref(v___x_4664_);
        v_queries_4666_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v_sz_4667_ = lean_array_size(v_fst_4665_);
        v___x_4668_ = 0usize;
        v___x_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4651_, v_fst_4665_, v_sz_4667_, v___x_4668_, v_queries_4666_, v_a_4653_);
        leanh::lean_dec(v_fst_4665_);
        return v___x_4669_;
    } else {
        let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4658_);
        leanh::lean_dec(v_requestedPos_4652_);
        leanh::lean_dec_ref(v_doc_4651_);
        v___x_4670_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v___x_4671_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4671_, 0, v___x_4670_);
        return v___x_4671_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries___boxed(
    mut v_doc_4672_: *mut leanh::LeanObject,
    mut v_requestedPos_4673_: *mut leanh::LeanObject,
    mut v_a_4674_: *mut leanh::LeanObject,
    mut v_a_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ =
        l_Lean_Server_FileWorker_computeQueries(v_doc_4672_, v_requestedPos_4673_, v_a_4674_);
    leanh::lean_dec_ref(v_a_4674_);
    return v_res_4676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(
    mut v_doc_4677_: *mut leanh::LeanObject,
    mut v_as_4678_: *mut leanh::LeanObject,
    mut v_sz_4679_: usize,
    mut v_i_4680_: usize,
    mut v_b_4681_: *mut leanh::LeanObject,
    mut v___y_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4677_, v_as_4678_, v_sz_4679_, v_i_4680_, v_b_4681_);
    return v___x_4684_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(
    mut v_doc_4685_: *mut leanh::LeanObject,
    mut v_as_4686_: *mut leanh::LeanObject,
    mut v_sz_4687_: *mut leanh::LeanObject,
    mut v_i_4688_: *mut leanh::LeanObject,
    mut v_b_4689_: *mut leanh::LeanObject,
    mut v___y_4690_: *mut leanh::LeanObject,
    mut v___y_4691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4692_: usize = 0;
    let mut v_i_boxed_4693_: usize = 0;
    let mut v_res_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4692_ = leanh::lean_unbox_usize(v_sz_4687_);
    leanh::lean_dec(v_sz_4687_);
    v_i_boxed_4693_ = leanh::lean_unbox_usize(v_i_4688_);
    leanh::lean_dec(v_i_4688_);
    v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_4685_, v_as_4686_, v_sz_boxed_4692_, v_i_boxed_4693_, v_b_4689_, v___y_4690_);
    leanh::lean_dec_ref(v___y_4690_);
    leanh::lean_dec_ref(v_as_4686_);
    return v_res_4694_;
}
pub unsafe fn l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
    mut v_params_4703_: *mut leanh::LeanObject,
    mut v_name_4704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = leanh::lean_unsigned_to_nat(0);
    v___x_4706_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4706_, 0, v_params_4703_);
    leanh::lean_ctor_set(v___x_4706_, 1, v_name_4704_);
    leanh::lean_ctor_set(v___x_4706_, 2, v___x_4705_);
    return v___x_4706_;
}
pub unsafe fn l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
    mut v_params_4708_: *mut leanh::LeanObject,
    mut v_kind_4709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = leanh::lean_box(0);
    v___x_4711_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0;
    v___x_4712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4712_, 0, v_kind_4709_);
    v___x_4713_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
    v___x_4714_ =
        l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_4708_, v___x_4713_);
    v___x_4715_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4714_);
    v___x_4716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4716_, 0, v___x_4715_);
    v___x_4717_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4717_, 0, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 1, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 2, v___x_4711_);
    leanh::lean_ctor_set(v___x_4717_, 3, v___x_4712_);
    leanh::lean_ctor_set(v___x_4717_, 4, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 5, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 6, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 7, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 8, v___x_4710_);
    leanh::lean_ctor_set(v___x_4717_, 9, v___x_4716_);
    return v___x_4717_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(
    mut v_ctx_4722_: *mut leanh::LeanObject,
    mut v_mod_4723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toCommandContextInfo_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: u8 = 0;
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toCommandContextInfo_4724_ = leanh::lean_ctor_get(v_ctx_4722_, 0);
    leanh::lean_inc_ref(v_toCommandContextInfo_4724_);
    v_parentDecl_x3f_4725_ = leanh::lean_ctor_get(v_ctx_4722_, 1);
    leanh::lean_inc(v_parentDecl_x3f_4725_);
    leanh::lean_dec_ref(v_ctx_4722_);
    v___x_4726_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0;
    v___x_4727_ = 1;
    v___x_4728_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4723_, v___x_4727_);
    v___x_4729_ = lean_string_append(v___x_4726_, v___x_4728_);
    leanh::lean_dec_ref(v___x_4728_);
    v___x_4730_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
    v_text_4731_ = lean_string_append(v___x_4729_, v___x_4730_);
    if leanh::lean_obj_tag(v_parentDecl_x3f_4725_) == 1 {
        let mut v_val_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: u8 = 0;
        v_val_4732_ = leanh::lean_ctor_get(v_parentDecl_x3f_4725_, 0);
        leanh::lean_inc_n(v_val_4732_, 2);
        leanh::lean_dec_ref_known(v_parentDecl_x3f_4725_, 1);
        v_env_4733_ = leanh::lean_ctor_get(v_toCommandContextInfo_4724_, 0);
        leanh::lean_inc_ref_n(v_env_4733_, 2);
        leanh::lean_dec_ref(v_toCommandContextInfo_4724_);
        v___x_4734_ = l_Lean_isMarkedMeta(v_env_4733_, v_val_4732_);
        if v___x_4734_ == 0 {
            let mut v_isExporting_4735_: u8 = 0;
            leanh::lean_dec(v_val_4732_);
            v_isExporting_4735_ = leanh::lean_ctor_get_uint8(
                v_env_4733_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
            );
            leanh::lean_dec_ref(v_env_4733_);
            if v_isExporting_4735_ == 0 {
                return v_text_4731_;
            } else {
                let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_text_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4736_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                v_text_4737_ = lean_string_append(v___x_4736_, v_text_4731_);
                leanh::lean_dec_ref(v_text_4731_);
                return v_text_4737_;
            }
        } else {
            let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_text_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4740_: u8 = 0;
            leanh::lean_dec_ref(v_env_4733_);
            v___x_4738_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3;
            v_text_4739_ = lean_string_append(v___x_4738_, v_text_4731_);
            leanh::lean_dec_ref(v_text_4731_);
            v___x_4740_ = l_Lean_isPrivateName(v_val_4732_);
            leanh::lean_dec(v_val_4732_);
            if v___x_4740_ == 0 {
                if v___x_4734_ == 0 {
                    return v_text_4739_;
                } else {
                    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_text_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4741_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                    v_text_4742_ = lean_string_append(v___x_4741_, v_text_4739_);
                    leanh::lean_dec_ref(v_text_4739_);
                    return v_text_4742_;
                }
            } else {
                return v_text_4739_;
            }
        }
    } else {
        leanh::lean_dec(v_parentDecl_x3f_4725_);
        leanh::lean_dec_ref(v_toCommandContextInfo_4724_);
        return v_text_4731_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(
    mut v_x_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_response_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_code_4764_: u8 = 0;
    let mut v_message_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4744_) == 0 {
                    v_response_4745_ = leanh::lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4763_ = (!leanh::lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4747_ = v_x_4744_;
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_response_4745_);
                        leanh::lean_dec(v_x_4744_);
                        v___x_4747_ = leanh::lean_box(0);
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_code_4764_ = leanh::lean_ctor_get_uint8(
                        v_x_4744_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_message_4765_ = leanh::lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4772_ = (!leanh::lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4772_ == 0 {
                        v___x_4767_ = v_x_4744_;
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_message_4765_);
                        leanh::lean_dec(v_x_4744_);
                        v___x_4767_ = leanh::lean_box(0);
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_response_4745_);
                v___x_4749_ =
                    l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_4745_);
                if leanh::lean_obj_tag(v___x_4749_) == 0 {
                    leanh::lean_del_object(v___x_4747_);
                    v_a_4750_ = leanh::lean_ctor_get(v___x_4749_, 0);
                    leanh::lean_inc(v_a_4750_);
                    leanh::lean_dec_ref_known(v___x_4749_, 1);
                    v___x_4751_ = 0;
                    v___x_4752_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0;
                    v___x_4753_ = l_Lean_Json_compress(v_response_4745_);
                    v___x_4754_ = lean_string_append(v___x_4752_, v___x_4753_);
                    leanh::lean_dec_ref(v___x_4753_);
                    v___x_4755_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
                    v___x_4756_ = lean_string_append(v___x_4754_, v___x_4755_);
                    v___x_4757_ = lean_string_append(v___x_4756_, v_a_4750_);
                    leanh::lean_dec(v_a_4750_);
                    v___x_4758_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_4758_, 0, v___x_4757_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4758_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4751_,
                    );
                    return v___x_4758_;
                } else {
                    leanh::lean_dec(v_response_4745_);
                    v_a_4759_ = leanh::lean_ctor_get(v___x_4749_, 0);
                    leanh::lean_inc(v_a_4759_);
                    leanh::lean_dec_ref_known(v___x_4749_, 1);
                    if v_isShared_4748_ == 0 {
                        leanh::lean_ctor_set(v___x_4747_, 0, v_a_4759_);
                        v___x_4761_ = v___x_4747_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4759_);
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
                    v_reuseFailAlloc_4771_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_message_4765_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_method_4774_: *mut leanh::LeanObject,
    mut v_param_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_serverRequestEmitter_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_serverRequestEmitter_4778_ = leanh::lean_ctor_get(v_a_4776_, 5);
    v___x_4779_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_4775_);
    leanh::lean_inc_ref(v_serverRequestEmitter_4778_);
    v___x_4780_ = leanh::lean_apply_3(
        v_serverRequestEmitter_4778_,
        v_method_4774_,
        v___x_4779_,
        leanh::lean_box(0),
    );
    v___f_4781_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0;
    v___x_4782_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4781_, v___x_4780_);
    v___x_4783_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4783_, 0, v___x_4782_);
    return v___x_4783_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(
    mut v_method_4784_: *mut leanh::LeanObject,
    mut v_param_4785_: *mut leanh::LeanObject,
    mut v_a_4786_: *mut leanh::LeanObject,
    mut v_a_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4788_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_4784_, v_param_4785_, v_a_4786_);
    leanh::lean_dec_ref(v_a_4786_);
    return v_res_4788_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(
    mut v_val_4789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4790_, 0, v_val_4789_);
    return v___x_4790_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(
    mut v_val_4791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4792_, 0, v_val_4791_);
    return v___x_4792_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(
    mut v_sz_4793_: usize,
    mut v_i_4794_: usize,
    mut v_bs_4795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4796_: u8 = 0;
    let mut v_v_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanModuleQuery_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: usize = 0;
    let mut v___x_4802_: usize = 0;
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
                if v___x_4796_ == 0 {
                    return v_bs_4795_;
                } else {
                    v_v_4797_ = lean_array_uget_borrowed(v_bs_4795_, v_i_4794_);
                    v_toLeanModuleQuery_4798_ = leanh::lean_ctor_get(v_v_4797_, 0);
                    leanh::lean_inc_ref(v_toLeanModuleQuery_4798_);
                    v___x_4799_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4805_: *mut leanh::LeanObject,
    mut v_i_4806_: *mut leanh::LeanObject,
    mut v_bs_4807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4808_: usize = 0;
    let mut v_i_boxed_4809_: usize = 0;
    let mut v_res_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4808_ = leanh::lean_unbox_usize(v_sz_4805_);
    leanh::lean_dec(v_sz_4805_);
    v_i_boxed_4809_ = leanh::lean_unbox_usize(v_i_4806_);
    leanh::lean_dec(v_i_4806_);
    v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_4808_, v_i_boxed_4809_, v_bs_4807_);
    return v_res_4810_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(
    mut v_a_4814_: *mut leanh::LeanObject,
    mut v_kind_4815_: *mut leanh::LeanObject,
    mut v___x_4816_: *mut leanh::LeanObject,
    mut v_params_4817_: *mut leanh::LeanObject,
    mut v___x_4818_: *mut leanh::LeanObject,
    mut v___x_4819_: *mut leanh::LeanObject,
    mut v_as_4820_: *mut leanh::LeanObject,
    mut v_sz_4821_: usize,
    mut v_i_4822_: usize,
    mut v_b_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_4835_: u8 = 0;
    let mut v_fst_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v_ctx_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4844_: u8 = 0;
    let mut v___y_4845_: u8 = 0;
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullName_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut v_fullName_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u8 = 0;
    let mut v___y_4924_: u8 = 0;
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v___x_4927_: u8 = 0;
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4830_ = lean_usize_dec_lt(v_i_4822_, v_sz_4821_);
                if v___x_4830_ == 0 {
                    leanh::lean_dec_ref(v___x_4818_);
                    leanh::lean_dec_ref(v_params_4817_);
                    leanh::lean_dec_ref(v___x_4816_);
                    leanh::lean_dec_ref(v_kind_4815_);
                    leanh::lean_dec_ref(v_a_4814_);
                    v___x_4831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4831_, 0, v_b_4823_);
                    return v___x_4831_;
                } else {
                    v_a_4832_ = lean_array_uget_borrowed(v_as_4820_, v_i_4822_);
                    v_module_4833_ = leanh::lean_ctor_get(v_a_4832_, 0);
                    v_decl_4834_ = leanh::lean_ctor_get(v_a_4832_, 1);
                    v_isExactMatch_4835_ = leanh::lean_ctor_get_uint8(
                        v_a_4832_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_fst_4836_ = leanh::lean_ctor_get(v_b_4823_, 0);
                    v_snd_4837_ = leanh::lean_ctor_get(v_b_4823_, 1);
                    v_isSharedCheck_4928_ = (!leanh::lean_is_exclusive(v_b_4823_)) as u8;
                    if v_isSharedCheck_4928_ == 0 {
                        v___x_4839_ = v_b_4823_;
                        v_isShared_4840_ = v_isSharedCheck_4928_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4837_);
                        leanh::lean_inc(v_fst_4836_);
                        leanh::lean_dec(v_b_4823_);
                        v___x_4839_ = leanh::lean_box(0);
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
                v_ctx_4841_ = leanh::lean_ctor_get(v_a_4814_, 1);
                v_determineInsertion_4842_ = leanh::lean_ctor_get(v_a_4814_, 2);
                v_toCommandContextInfo_4919_ = leanh::lean_ctor_get(v_ctx_4841_, 0);
                v_env_4920_ = leanh::lean_ctor_get(v_toCommandContextInfo_4919_, 0);
                v___x_4921_ = leanh::lean_unsigned_to_nat(0);
                v___x_4922_ = lean_nat_dec_eq(v___x_4819_, v___x_4921_);
                leanh::lean_inc(v_decl_4834_);
                leanh::lean_inc_ref(v_env_4920_);
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
                    leanh::lean_inc_ref(v_determineInsertion_4842_);
                    leanh::lean_inc(v_decl_4834_);
                    v___x_4846_ =
                        leanh::lean_apply_1(v_determineInsertion_4842_, v_decl_4834_);
                    if v___y_4844_ == 0 {
                        v_fullName_4847_ = leanh::lean_ctor_get(v___x_4846_, 0);
                        v_edit_4848_ = leanh::lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4875_ =
                            (!leanh::lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4875_ == 0 {
                            v___x_4850_ = v___x_4846_;
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_edit_4848_);
                            leanh::lean_inc(v_fullName_4847_);
                            leanh::lean_dec(v___x_4846_);
                            v___x_4850_ = leanh::lean_box(0);
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_fullName_4876_ = leanh::lean_ctor_get(v___x_4846_, 0);
                        v_edit_4877_ = leanh::lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4915_ =
                            (!leanh::lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4915_ == 0 {
                            v___x_4879_ = v___x_4846_;
                            v_isShared_4880_ = v_isSharedCheck_4915_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_edit_4877_);
                            leanh::lean_inc(v_fullName_4876_);
                            leanh::lean_dec(v___x_4846_);
                            v___x_4879_ = leanh::lean_box(0);
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
                        v_reuseFailAlloc_4918_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_fst_4836_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_snd_4837_);
                        v___x_4917_ = v_reuseFailAlloc_4918_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4852_ = leanh::lean_box(0);
                v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
                v___x_4854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4847_,
                    v___x_4830_,
                );
                v___x_4855_ = lean_string_append(v___x_4853_, v___x_4854_);
                leanh::lean_dec_ref(v___x_4854_);
                leanh::lean_inc_ref(v_kind_4815_);
                v___x_4856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4856_, 0, v_kind_4815_);
                leanh::lean_inc_ref(v___x_4816_);
                v___x_4857_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                v___x_4858_ = leanh::lean_unsigned_to_nat(1);
                v___x_4859_ = lean_mk_empty_array_with_capacity(v___x_4858_);
                v___x_4860_ = lean_array_push(v___x_4859_, v_edit_4848_);
                if v_isShared_4851_ == 0 {
                    leanh::lean_ctor_set(v___x_4850_, 1, v___x_4860_);
                    leanh::lean_ctor_set(v___x_4850_, 0, v___x_4857_);
                    v___x_4862_ = v___x_4850_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4860_);
                    v___x_4862_ = v_reuseFailAlloc_4874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4863_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4862_);
                v___x_4864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4864_, 0, v___x_4863_);
                v___x_4865_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                leanh::lean_inc_ref(v_params_4817_);
                v___x_4866_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4865_,
                );
                v___x_4867_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4866_);
                v___x_4868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4868_, 0, v___x_4867_);
                v___x_4869_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                leanh::lean_ctor_set(v___x_4869_, 0, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 1, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 2, v___x_4855_);
                leanh::lean_ctor_set(v___x_4869_, 3, v___x_4856_);
                leanh::lean_ctor_set(v___x_4869_, 4, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 5, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 6, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 7, v___x_4864_);
                leanh::lean_ctor_set(v___x_4869_, 8, v___x_4852_);
                leanh::lean_ctor_set(v___x_4869_, 9, v___x_4868_);
                v___x_4870_ = lean_array_push(v_fst_4836_, v___x_4869_);
                if v_isShared_4840_ == 0 {
                    leanh::lean_ctor_set(v___x_4839_, 0, v___x_4870_);
                    v___x_4872_ = v___x_4839_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 1, v_snd_4837_);
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
                v___x_4881_ = leanh::lean_box(0);
                v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
                v___x_4883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4876_,
                    v___y_4844_,
                );
                v___x_4884_ = lean_string_append(v___x_4882_, v___x_4883_);
                leanh::lean_dec_ref(v___x_4883_);
                v___x_4885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
                v___x_4886_ = lean_string_append(v___x_4884_, v___x_4885_);
                leanh::lean_inc_n(v_module_4833_, 2);
                v___x_4887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_module_4833_,
                    v___y_4844_,
                );
                v___x_4888_ = lean_string_append(v___x_4886_, v___x_4887_);
                leanh::lean_dec_ref(v___x_4887_);
                leanh::lean_inc_ref(v_kind_4815_);
                v___x_4889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4889_, 0, v_kind_4815_);
                leanh::lean_inc_ref(v___x_4816_);
                v___x_4890_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                leanh::lean_inc_ref(v_ctx_4841_);
                v___x_4891_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_4841_, v_module_4833_);
                leanh::lean_inc_ref(v___x_4818_);
                v___x_4892_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4892_, 0, v___x_4818_);
                leanh::lean_ctor_set(v___x_4892_, 1, v___x_4891_);
                leanh::lean_ctor_set(v___x_4892_, 2, v___x_4881_);
                leanh::lean_ctor_set(v___x_4892_, 3, v___x_4881_);
                v___x_4893_ = leanh::lean_unsigned_to_nat(2);
                v___x_4894_ = lean_mk_empty_array_with_capacity(v___x_4893_);
                v___x_4895_ = lean_array_push(v___x_4894_, v___x_4892_);
                v___x_4896_ = lean_array_push(v___x_4895_, v_edit_4877_);
                if v_isShared_4880_ == 0 {
                    leanh::lean_ctor_set(v___x_4879_, 1, v___x_4896_);
                    leanh::lean_ctor_set(v___x_4879_, 0, v___x_4890_);
                    v___x_4898_ = v___x_4879_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4890_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4896_);
                    v___x_4898_ = v_reuseFailAlloc_4914_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4899_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4898_);
                v___x_4900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4900_, 0, v___x_4899_);
                v___x_4901_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                leanh::lean_inc_ref(v_params_4817_);
                v___x_4902_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4901_,
                );
                v___x_4903_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4902_);
                v___x_4904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
                v___x_4905_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                leanh::lean_ctor_set(v___x_4905_, 0, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 1, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 2, v___x_4888_);
                leanh::lean_ctor_set(v___x_4905_, 3, v___x_4889_);
                leanh::lean_ctor_set(v___x_4905_, 4, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 5, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 6, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 7, v___x_4900_);
                leanh::lean_ctor_set(v___x_4905_, 8, v___x_4881_);
                leanh::lean_ctor_set(v___x_4905_, 9, v___x_4904_);
                v___x_4906_ = lean_array_push(v_fst_4836_, v___x_4905_);
                if v_isExactMatch_4835_ == 0 {
                    if v_isShared_4840_ == 0 {
                        leanh::lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4908_ = v___x_4839_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4909_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4906_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_snd_4837_);
                        v___x_4908_ = v_reuseFailAlloc_4909_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_4837_);
                    v___x_4910_ = leanh::lean_box((v___x_4830_) as usize);
                    if v_isShared_4840_ == 0 {
                        leanh::lean_ctor_set(v___x_4839_, 1, v___x_4910_);
                        leanh::lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4912_ = v___x_4839_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4913_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4906_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 1, v___x_4910_);
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
                    leanh::lean_dec(v___x_4925_);
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
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_kind_4930_: *mut leanh::LeanObject,
    mut v___x_4931_: *mut leanh::LeanObject,
    mut v_params_4932_: *mut leanh::LeanObject,
    mut v___x_4933_: *mut leanh::LeanObject,
    mut v___x_4934_: *mut leanh::LeanObject,
    mut v_as_4935_: *mut leanh::LeanObject,
    mut v_sz_4936_: *mut leanh::LeanObject,
    mut v_i_4937_: *mut leanh::LeanObject,
    mut v_b_4938_: *mut leanh::LeanObject,
    mut v___y_4939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4940_: usize = 0;
    let mut v_i_boxed_4941_: usize = 0;
    let mut v_res_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4940_ = leanh::lean_unbox_usize(v_sz_4936_);
    leanh::lean_dec(v_sz_4936_);
    v_i_boxed_4941_ = leanh::lean_unbox_usize(v_i_4937_);
    leanh::lean_dec(v_i_4937_);
    v_res_4942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4929_, v_kind_4930_, v___x_4931_, v_params_4932_, v___x_4933_, v___x_4934_, v_as_4935_, v_sz_boxed_4940_, v_i_boxed_4941_, v_b_4938_);
    leanh::lean_dec_ref(v_as_4935_);
    leanh::lean_dec(v___x_4934_);
    return v_res_4942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(
    mut v_kind_4943_: *mut leanh::LeanObject,
    mut v___x_4944_: *mut leanh::LeanObject,
    mut v_params_4945_: *mut leanh::LeanObject,
    mut v___x_4946_: *mut leanh::LeanObject,
    mut v___x_4947_: *mut leanh::LeanObject,
    mut v_as_4948_: *mut leanh::LeanObject,
    mut v_sz_4949_: usize,
    mut v_i_4950_: usize,
    mut v_b_4951_: *mut leanh::LeanObject,
    mut v___y_4952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v_fst_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v_array_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: u8 = 0;
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_a_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4984_: usize = 0;
    let mut v___x_4985_: usize = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v_reuseFailAlloc_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_a_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_reuseFailAlloc_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut v_unused_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v_unused_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4954_ = lean_usize_dec_lt(v_i_4950_, v_sz_4949_);
                if v___x_4954_ == 0 {
                    leanh::lean_dec_ref(v___x_4946_);
                    leanh::lean_dec_ref(v_params_4945_);
                    leanh::lean_dec_ref(v___x_4944_);
                    leanh::lean_dec_ref(v_kind_4943_);
                    v___x_4955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4955_, 0, v_b_4951_);
                    return v___x_4955_;
                } else {
                    v_snd_4956_ = leanh::lean_ctor_get(v_b_4951_, 1);
                    leanh::lean_inc(v_snd_4956_);
                    v_snd_4957_ = leanh::lean_ctor_get(v_snd_4956_, 1);
                    leanh::lean_inc(v_snd_4957_);
                    v_fst_4958_ = leanh::lean_ctor_get(v_b_4951_, 0);
                    v_isSharedCheck_5023_ = (!leanh::lean_is_exclusive(v_b_4951_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v_unused_5024_ = leanh::lean_ctor_get(v_b_4951_, 1);
                        leanh::lean_dec(v_unused_5024_);
                        v___x_4960_ = v_b_4951_;
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_4958_);
                        leanh::lean_dec(v_b_4951_);
                        v___x_4960_ = leanh::lean_box(0);
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4962_ = leanh::lean_ctor_get(v_snd_4956_, 0);
                v_isSharedCheck_5021_ = (!leanh::lean_is_exclusive(v_snd_4956_)) as u8;
                if v_isSharedCheck_5021_ == 0 {
                    v_unused_5022_ = leanh::lean_ctor_get(v_snd_4956_, 1);
                    leanh::lean_dec(v_unused_5022_);
                    v___x_4964_ = v_snd_4956_;
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4962_);
                    leanh::lean_dec(v_snd_4956_);
                    v___x_4964_ = leanh::lean_box(0);
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_array_4966_ = leanh::lean_ctor_get(v_snd_4957_, 0);
                v_start_4967_ = leanh::lean_ctor_get(v_snd_4957_, 1);
                v_stop_4968_ = leanh::lean_ctor_get(v_snd_4957_, 2);
                v___x_4969_ = lean_nat_dec_lt(v_start_4967_, v_stop_4968_);
                if v___x_4969_ == 0 {
                    leanh::lean_dec_ref(v___x_4946_);
                    leanh::lean_dec_ref(v_params_4945_);
                    leanh::lean_dec_ref(v___x_4944_);
                    leanh::lean_dec_ref(v_kind_4943_);
                    if v_isShared_4965_ == 0 {
                        v___x_4971_ = v___x_4964_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4976_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_fst_4962_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 1, v_snd_4957_);
                        v___x_4971_ = v_reuseFailAlloc_4976_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_4968_);
                    leanh::lean_inc(v_start_4967_);
                    leanh::lean_inc_ref(v_array_4966_);
                    v_isSharedCheck_5017_ = (!leanh::lean_is_exclusive(v_snd_4957_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = leanh::lean_ctor_get(v_snd_4957_, 2);
                        leanh::lean_dec(v_unused_5018_);
                        v_unused_5019_ = leanh::lean_ctor_get(v_snd_4957_, 1);
                        leanh::lean_dec(v_unused_5019_);
                        v_unused_5020_ = leanh::lean_ctor_get(v_snd_4957_, 0);
                        leanh::lean_dec(v_unused_5020_);
                        v___x_4978_ = v_snd_4957_;
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_4957_);
                        v___x_4978_ = leanh::lean_box(0);
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4961_ == 0 {
                    leanh::lean_ctor_set(v___x_4960_, 1, v___x_4971_);
                    v___x_4973_ = v___x_4960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_fst_4958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4971_);
                    v___x_4973_ = v_reuseFailAlloc_4975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4974_, 0, v___x_4973_);
                return v___x_4974_;
            }
            5 => {
                v_a_4980_ = lean_array_uget_borrowed(v_as_4948_, v_i_4950_);
                v___x_4981_ = lean_array_fget_borrowed(v_array_4966_, v_start_4967_);
                if v_isShared_4965_ == 0 {
                    leanh::lean_ctor_set(v___x_4964_, 1, v_fst_4962_);
                    leanh::lean_ctor_set(v___x_4964_, 0, v_fst_4958_);
                    v___x_4983_ = v___x_4964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_fst_4958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_fst_4962_);
                    v___x_4983_ = v_reuseFailAlloc_5016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_sz_4984_ = lean_array_size(v___x_4981_);
                v___x_4985_ = 0usize;
                leanh::lean_inc_ref(v___x_4946_);
                leanh::lean_inc_ref(v_params_4945_);
                leanh::lean_inc_ref(v___x_4944_);
                leanh::lean_inc_ref(v_kind_4943_);
                leanh::lean_inc(v_a_4980_);
                v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4980_, v_kind_4943_, v___x_4944_, v_params_4945_, v___x_4946_, v___x_4947_, v___x_4981_, v_sz_4984_, v___x_4985_, v___x_4983_);
                if leanh::lean_obj_tag(v___x_4986_) == 0 {
                    v_a_4987_ = leanh::lean_ctor_get(v___x_4986_, 0);
                    leanh::lean_inc(v_a_4987_);
                    leanh::lean_dec_ref_known(v___x_4986_, 1);
                    v_fst_4988_ = leanh::lean_ctor_get(v_a_4987_, 0);
                    v_snd_4989_ = leanh::lean_ctor_get(v_a_4987_, 1);
                    v_isSharedCheck_5007_ = (!leanh::lean_is_exclusive(v_a_4987_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_4991_ = v_a_4987_;
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4989_);
                        leanh::lean_inc(v_fst_4988_);
                        leanh::lean_dec(v_a_4987_);
                        v___x_4991_ = leanh::lean_box(0);
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4978_);
                    leanh::lean_dec(v_stop_4968_);
                    leanh::lean_dec(v_start_4967_);
                    leanh::lean_dec_ref(v_array_4966_);
                    leanh::lean_del_object(v___x_4960_);
                    leanh::lean_dec_ref(v___x_4946_);
                    leanh::lean_dec_ref(v_params_4945_);
                    leanh::lean_dec_ref(v___x_4944_);
                    leanh::lean_dec_ref(v_kind_4943_);
                    v_a_5008_ = leanh::lean_ctor_get(v___x_4986_, 0);
                    v_isSharedCheck_5015_ = (!leanh::lean_is_exclusive(v___x_4986_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5010_ = v___x_4986_;
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5008_);
                        leanh::lean_dec(v___x_4986_);
                        v___x_5010_ = leanh::lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4993_ = leanh::lean_unsigned_to_nat(1);
                v___x_4994_ = lean_nat_add(v_start_4967_, v___x_4993_);
                leanh::lean_dec(v_start_4967_);
                if v_isShared_4979_ == 0 {
                    leanh::lean_ctor_set(v___x_4978_, 1, v___x_4994_);
                    v___x_4996_ = v___x_4978_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_array_4966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 1, v___x_4994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 2, v_stop_4968_);
                    v___x_4996_ = v_reuseFailAlloc_5006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4992_ == 0 {
                    leanh::lean_ctor_set(v___x_4991_, 1, v___x_4996_);
                    leanh::lean_ctor_set(v___x_4991_, 0, v_snd_4989_);
                    v___x_4998_ = v___x_4991_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_snd_4989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_5005_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4961_ == 0 {
                    leanh::lean_ctor_set(v___x_4960_, 1, v___x_4998_);
                    leanh::lean_ctor_set(v___x_4960_, 0, v_fst_4988_);
                    v___x_5000_ = v___x_4960_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_fst_4988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 1, v___x_4998_);
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
                    v_reuseFailAlloc_5014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
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
    mut v_kind_5025_: *mut leanh::LeanObject,
    mut v___x_5026_: *mut leanh::LeanObject,
    mut v_params_5027_: *mut leanh::LeanObject,
    mut v___x_5028_: *mut leanh::LeanObject,
    mut v___x_5029_: *mut leanh::LeanObject,
    mut v_as_5030_: *mut leanh::LeanObject,
    mut v_sz_5031_: *mut leanh::LeanObject,
    mut v_i_5032_: *mut leanh::LeanObject,
    mut v_b_5033_: *mut leanh::LeanObject,
    mut v___y_5034_: *mut leanh::LeanObject,
    mut v___y_5035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5036_: usize = 0;
    let mut v_i_boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5036_ = leanh::lean_unbox_usize(v_sz_5031_);
    leanh::lean_dec(v_sz_5031_);
    v_i_boxed_5037_ = leanh::lean_unbox_usize(v_i_5032_);
    leanh::lean_dec(v_i_5032_);
    v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5025_, v___x_5026_, v_params_5027_, v___x_5028_, v___x_5029_, v_as_5030_, v_sz_boxed_5036_, v_i_boxed_5037_, v_b_5033_, v___y_5034_);
    leanh::lean_dec_ref(v___y_5034_);
    leanh::lean_dec_ref(v_as_5030_);
    leanh::lean_dec(v___x_5029_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
    mut v_id_5047_: *mut leanh::LeanObject,
    mut v_params_5048_: *mut leanh::LeanObject,
    mut v_requestedRange_5049_: *mut leanh::LeanObject,
    mut v_kind_5050_: *mut leanh::LeanObject,
    mut v_a_5051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_doc_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5059_: u8 = 0;
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: u8 = 0;
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___f_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_unused_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_val_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v_snd_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v_fst_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_initSnap_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5162_: u8 = 0;
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_unused_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut v_reuseFailAlloc_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_unused_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5053_ = leanh::lean_ctor_get(v_a_5051_, 1);
                v_cancelTk_5054_ = leanh::lean_ctor_get(v_a_5051_, 4);
                v_toEditableDocumentCore_5055_ = leanh::lean_ctor_get(v_doc_5053_, 0);
                v_stop_5056_ = leanh::lean_ctor_get(v_requestedRange_5049_, 1);
                v_isSharedCheck_5185_ =
                    (!leanh::lean_is_exclusive(v_requestedRange_5049_)) as u8;
                if v_isSharedCheck_5185_ == 0 {
                    v_unused_5186_ = leanh::lean_ctor_get(v_requestedRange_5049_, 0);
                    leanh::lean_dec(v_unused_5186_);
                    v___x_5058_ = v_requestedRange_5049_;
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_5056_);
                    leanh::lean_dec(v_requestedRange_5049_);
                    v___x_5058_ = leanh::lean_box(0);
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_doc_5053_);
                v___x_5060_ =
                    l_Lean_Server_FileWorker_computeQueries(v_doc_5053_, v_stop_5056_, v_a_5051_);
                if leanh::lean_obj_tag(v___x_5060_) == 0 {
                    v_a_5061_ = leanh::lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5176_ = (!leanh::lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5063_ = v___x_5060_;
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5061_);
                        leanh::lean_dec(v___x_5060_);
                        v___x_5063_ = leanh::lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5058_);
                    leanh::lean_dec_ref(v_kind_5050_);
                    leanh::lean_dec_ref(v_params_5048_);
                    leanh::lean_dec(v_id_5047_);
                    v_a_5177_ = leanh::lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5184_ = (!leanh::lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5184_ == 0 {
                        v___x_5179_ = v___x_5060_;
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5177_);
                        leanh::lean_dec(v___x_5060_);
                        v___x_5179_ = leanh::lean_box(0);
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5065_ = lean_array_get_size(v_a_5061_);
                v___x_5066_ = leanh::lean_unsigned_to_nat(0);
                v___x_5067_ = lean_nat_dec_eq(v___x_5065_, v___x_5066_);
                if v___x_5067_ == 0 {
                    leanh::lean_del_object(v___x_5063_);
                    v___x_5068_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5069_ = lean_array_size(v_a_5061_);
                    v___x_5070_ = 0usize;
                    leanh::lean_inc(v_a_5061_);
                    v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5069_, v___x_5070_, v_a_5061_);
                    if v_isShared_5059_ == 0 {
                        leanh::lean_ctor_set(v___x_5058_, 1, v___x_5071_);
                        leanh::lean_ctor_set(v___x_5058_, 0, v_id_5047_);
                        v___x_5073_ = v___x_5058_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_id_5047_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 1, v___x_5071_);
                        v___x_5073_ = v_reuseFailAlloc_5171_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5061_);
                    leanh::lean_del_object(v___x_5058_);
                    leanh::lean_dec_ref(v_kind_5050_);
                    leanh::lean_dec_ref(v_params_5048_);
                    leanh::lean_dec(v_id_5047_);
                    v___x_5172_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                    if v_isShared_5064_ == 0 {
                        leanh::lean_ctor_set(v___x_5063_, 0, v___x_5172_);
                        v___x_5174_ = v___x_5063_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_5175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
                        v___x_5174_ = v_reuseFailAlloc_5175_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5074_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5068_, v___x_5073_, v_a_5051_);
                v_a_5075_ = leanh::lean_ctor_get(v___x_5074_, 0);
                v_isSharedCheck_5170_ = (!leanh::lean_is_exclusive(v___x_5074_)) as u8;
                if v_isSharedCheck_5170_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    v_isShared_5078_ = v_isSharedCheck_5170_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5075_);
                    leanh::lean_dec(v___x_5074_);
                    v___x_5077_ = leanh::lean_box(0);
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
                v___x_5084_ = leanh::lean_box(0);
                v___x_5085_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5085_, 0, v___x_5083_);
                leanh::lean_ctor_set(v___x_5085_, 1, v___x_5084_);
                v___x_5086_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5086_, 0, v___x_5081_);
                leanh::lean_ctor_set(v___x_5086_, 1, v___x_5085_);
                v___x_5087_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_5086_);
                if leanh::lean_obj_tag(v___x_5087_) == 0 {
                    v_val_5108_ = leanh::lean_ctor_get(v___x_5087_, 0);
                    leanh::lean_inc(v_val_5108_);
                    leanh::lean_dec_ref_known(v___x_5087_, 1);
                    if leanh::lean_obj_tag(v_val_5108_) == 0 {
                        v_response_5109_ = leanh::lean_ctor_get(v_val_5108_, 0);
                        leanh::lean_inc(v_response_5109_);
                        leanh::lean_dec_ref_known(v_val_5108_, 1);
                        v_initSnap_5151_ =
                            leanh::lean_ctor_get(v_toEditableDocumentCore_5055_, 1);
                        v_meta_5152_ =
                            leanh::lean_ctor_get(v_toEditableDocumentCore_5055_, 0);
                        v_stx_5153_ = leanh::lean_ctor_get(v_initSnap_5151_, 3);
                        v___x_5154_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5153_, v___x_5067_);
                        if leanh::lean_obj_tag(v___x_5154_) == 0 {
                            v___x_5155_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5;
                            v___y_5111_ = v___x_5155_;
                            state = 10;
                            continue;
                        } else {
                            v_val_5156_ = leanh::lean_ctor_get(v___x_5154_, 0);
                            leanh::lean_inc(v_val_5156_);
                            leanh::lean_dec_ref_known(v___x_5154_, 1);
                            v_text_5157_ = leanh::lean_ctor_get(v_meta_5152_, 3);
                            leanh::lean_inc_ref(v_text_5157_);
                            v___x_5158_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5157_, v_val_5156_);
                            leanh::lean_dec(v_val_5156_);
                            v_line_5159_ = leanh::lean_ctor_get(v___x_5158_, 0);
                            v_isSharedCheck_5168_ =
                                (!leanh::lean_is_exclusive(v___x_5158_)) as u8;
                            if v_isSharedCheck_5168_ == 0 {
                                v_unused_5169_ = leanh::lean_ctor_get(v___x_5158_, 1);
                                leanh::lean_dec(v_unused_5169_);
                                v___x_5161_ = v___x_5158_;
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_line_5159_);
                                leanh::lean_dec(v___x_5158_);
                                v___x_5161_ = leanh::lean_box(0);
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_5108_);
                        leanh::lean_del_object(v___x_5077_);
                        leanh::lean_dec(v_a_5061_);
                        leanh::lean_dec_ref(v_kind_5050_);
                        leanh::lean_dec_ref(v_params_5048_);
                        v___y_5089_ = v_a_5051_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5087_);
                    leanh::lean_del_object(v___x_5077_);
                    leanh::lean_dec(v_a_5061_);
                    leanh::lean_dec_ref(v_kind_5050_);
                    leanh::lean_dec_ref(v_params_5048_);
                    v___y_5089_ = v_a_5051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5090_ = l_Lean_Server_RequestM_checkCancelled(v___y_5089_);
                if leanh::lean_obj_tag(v___x_5090_) == 0 {
                    v_isSharedCheck_5098_ = (!leanh::lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5098_ == 0 {
                        v_unused_5099_ = leanh::lean_ctor_get(v___x_5090_, 0);
                        leanh::lean_dec(v_unused_5099_);
                        v___x_5092_ = v___x_5090_;
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5090_);
                        v___x_5092_ = leanh::lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_5100_ = leanh::lean_ctor_get(v___x_5090_, 0);
                    v_isSharedCheck_5107_ = (!leanh::lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5102_ = v___x_5090_;
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5100_);
                        leanh::lean_dec(v___x_5090_);
                        v___x_5102_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5092_, 0, v___x_5094_);
                    v___x_5096_ = v___x_5092_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
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
                    v_reuseFailAlloc_5106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5105_;
            }
            10 => {
                leanh::lean_inc_ref(v___y_5111_);
                v___x_5112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5112_, 0, v___y_5111_);
                leanh::lean_ctor_set(v___x_5112_, 1, v___y_5111_);
                v___x_5113_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                v___x_5114_ = lean_array_get_size(v_response_5109_);
                v___x_5115_ = lean_nat_dec_lt(v___x_5066_, v___x_5114_);
                if v___x_5115_ == 0 {
                    leanh::lean_dec_ref_known(v___x_5112_, 2);
                    leanh::lean_dec(v_response_5109_);
                    leanh::lean_dec(v_a_5061_);
                    leanh::lean_dec_ref(v_kind_5050_);
                    leanh::lean_dec_ref(v_params_5048_);
                    if v_isShared_5078_ == 0 {
                        leanh::lean_ctor_set(v___x_5077_, 0, v___x_5113_);
                        v___x_5117_ = v___x_5077_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5113_);
                        v___x_5117_ = v_reuseFailAlloc_5118_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5077_);
                    v___x_5119_ =
                        l_Array_toSubarray___redArg(v_response_5109_, v___x_5066_, v___x_5114_);
                    v___x_5120_ = leanh::lean_box((v___x_5067_) as usize);
                    v___x_5121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5121_, 0, v___x_5120_);
                    leanh::lean_ctor_set(v___x_5121_, 1, v___x_5119_);
                    v___x_5122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5122_, 0, v___x_5113_);
                    leanh::lean_ctor_set(v___x_5122_, 1, v___x_5121_);
                    leanh::lean_inc_ref(v_params_5048_);
                    leanh::lean_inc_ref(v_doc_5053_);
                    v___x_5123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5050_, v_doc_5053_, v_params_5048_, v___x_5112_, v___x_5065_, v_a_5061_, v_sz_5069_, v___x_5070_, v___x_5122_, v_a_5051_);
                    leanh::lean_dec(v_a_5061_);
                    if leanh::lean_obj_tag(v___x_5123_) == 0 {
                        v_a_5124_ = leanh::lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5142_ =
                            (!leanh::lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v___x_5126_ = v___x_5123_;
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5124_);
                            leanh::lean_dec(v___x_5123_);
                            v___x_5126_ = leanh::lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_params_5048_);
                        v_a_5143_ = leanh::lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5150_ =
                            (!leanh::lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5123_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5143_);
                            leanh::lean_dec(v___x_5123_);
                            v___x_5145_ = leanh::lean_box(0);
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
                v_snd_5128_ = leanh::lean_ctor_get(v_a_5124_, 1);
                v_fst_5129_ = leanh::lean_ctor_get(v_snd_5128_, 0);
                v___x_5130_ = (leanh::lean_unbox(v_fst_5129_) as u8);
                if v___x_5130_ == 0 {
                    leanh::lean_dec_ref(v_params_5048_);
                    v_fst_5131_ = leanh::lean_ctor_get(v_a_5124_, 0);
                    leanh::lean_inc(v_fst_5131_);
                    leanh::lean_dec(v_a_5124_);
                    if v_isShared_5127_ == 0 {
                        leanh::lean_ctor_set(v___x_5126_, 0, v_fst_5131_);
                        v___x_5133_ = v___x_5126_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_fst_5131_);
                        v___x_5133_ = v_reuseFailAlloc_5134_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_fst_5135_ = leanh::lean_ctor_get(v_a_5124_, 0);
                    leanh::lean_inc(v_fst_5135_);
                    leanh::lean_dec(v_a_5124_);
                    v___x_5136_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4;
                    v___x_5137_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
                        v_params_5048_,
                        v___x_5136_,
                    );
                    v___x_5138_ = lean_array_push(v_fst_5135_, v___x_5137_);
                    if v_isShared_5127_ == 0 {
                        leanh::lean_ctor_set(v___x_5126_, 0, v___x_5138_);
                        v___x_5140_ = v___x_5126_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
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
                    v_reuseFailAlloc_5149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5148_;
            }
            17 => {
                v___x_5163_ = leanh::lean_unsigned_to_nat(1);
                v___x_5164_ = lean_nat_add(v_line_5159_, v___x_5163_);
                leanh::lean_dec(v_line_5159_);
                if v_isShared_5162_ == 0 {
                    leanh::lean_ctor_set(v___x_5161_, 1, v___x_5066_);
                    leanh::lean_ctor_set(v___x_5161_, 0, v___x_5164_);
                    v___x_5166_ = v___x_5161_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5066_);
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
                    v_reuseFailAlloc_5183_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
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
    mut v_id_5187_: *mut leanh::LeanObject,
    mut v_params_5188_: *mut leanh::LeanObject,
    mut v_requestedRange_5189_: *mut leanh::LeanObject,
    mut v_kind_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
    mut v_a_5192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
        v_id_5187_,
        v_params_5188_,
        v_requestedRange_5189_,
        v_kind_5190_,
        v_a_5191_,
    );
    leanh::lean_dec_ref(v_a_5191_);
    return v_res_5193_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_kind_5195_: *mut leanh::LeanObject,
    mut v___x_5196_: *mut leanh::LeanObject,
    mut v_params_5197_: *mut leanh::LeanObject,
    mut v___x_5198_: *mut leanh::LeanObject,
    mut v___x_5199_: *mut leanh::LeanObject,
    mut v_as_5200_: *mut leanh::LeanObject,
    mut v_sz_5201_: usize,
    mut v_i_5202_: usize,
    mut v_b_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_5194_, v_kind_5195_, v___x_5196_, v_params_5197_, v___x_5198_, v___x_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_);
    return v___x_5206_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(
    mut v_a_5207_: *mut leanh::LeanObject,
    mut v_kind_5208_: *mut leanh::LeanObject,
    mut v___x_5209_: *mut leanh::LeanObject,
    mut v_params_5210_: *mut leanh::LeanObject,
    mut v___x_5211_: *mut leanh::LeanObject,
    mut v___x_5212_: *mut leanh::LeanObject,
    mut v_as_5213_: *mut leanh::LeanObject,
    mut v_sz_5214_: *mut leanh::LeanObject,
    mut v_i_5215_: *mut leanh::LeanObject,
    mut v_b_5216_: *mut leanh::LeanObject,
    mut v___y_5217_: *mut leanh::LeanObject,
    mut v___y_5218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5219_: usize = 0;
    let mut v_i_boxed_5220_: usize = 0;
    let mut v_res_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5219_ = leanh::lean_unbox_usize(v_sz_5214_);
    leanh::lean_dec(v_sz_5214_);
    v_i_boxed_5220_ = leanh::lean_unbox_usize(v_i_5215_);
    leanh::lean_dec(v_i_5215_);
    v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_5207_, v_kind_5208_, v___x_5209_, v_params_5210_, v___x_5211_, v___x_5212_, v_as_5213_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5216_, v___y_5217_);
    leanh::lean_dec_ref(v___y_5217_);
    leanh::lean_dec_ref(v_as_5213_);
    leanh::lean_dec(v___x_5212_);
    return v_res_5221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(
    mut v_a_5225_: *mut leanh::LeanObject,
    mut v_as_5226_: *mut leanh::LeanObject,
    mut v_sz_5227_: usize,
    mut v_i_5228_: usize,
    mut v_b_5229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: usize = 0;
    let mut v___x_5235_: u8 = 0;
    let mut v_a_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_5238_: u8 = 0;
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
                if v___x_5235_ == 0 {
                    leanh::lean_dec_ref(v_a_5225_);
                    leanh::lean_inc_ref(v_b_5229_);
                    return v_b_5229_;
                } else {
                    v_a_5236_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
                    v_decl_5237_ = leanh::lean_ctor_get(v_a_5236_, 1);
                    v_isExactMatch_5238_ = leanh::lean_ctor_get_uint8(
                        v_a_5236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_5239_ = leanh::lean_box(0);
                    v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                    if v_isExactMatch_5238_ == 0 {
                        v_a_5231_ = v___x_5240_;
                        state = 1;
                        continue;
                    } else {
                        v_ctx_5241_ = leanh::lean_ctor_get(v_a_5225_, 1);
                        v_toCommandContextInfo_5242_ = leanh::lean_ctor_get(v_ctx_5241_, 0);
                        v_env_5243_ = leanh::lean_ctor_get(v_toCommandContextInfo_5242_, 0);
                        leanh::lean_inc(v_decl_5237_);
                        leanh::lean_inc_ref(v_env_5243_);
                        v___x_5244_ = l_Lean_Environment_contains(
                            v_env_5243_,
                            v_decl_5237_,
                            v_isExactMatch_5238_,
                        );
                        if v___x_5244_ == 0 {
                            leanh::lean_dec_ref(v_a_5225_);
                            leanh::lean_inc(v_a_5236_);
                            v___x_5245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5245_, 0, v_a_5236_);
                            v___x_5246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5246_, 0, v___x_5245_);
                            v___x_5247_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                            leanh::lean_ctor_set(v___x_5247_, 1, v___x_5239_);
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
    mut v_a_5248_: *mut leanh::LeanObject,
    mut v_as_5249_: *mut leanh::LeanObject,
    mut v_sz_5250_: *mut leanh::LeanObject,
    mut v_i_5251_: *mut leanh::LeanObject,
    mut v_b_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5253_: usize = 0;
    let mut v_i_boxed_5254_: usize = 0;
    let mut v_res_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5253_ = leanh::lean_unbox_usize(v_sz_5250_);
    leanh::lean_dec(v_sz_5250_);
    v_i_boxed_5254_ = leanh::lean_unbox_usize(v_i_5251_);
    leanh::lean_dec(v_i_5251_);
    v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5248_, v_as_5249_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5252_);
    leanh::lean_dec_ref(v_b_5252_);
    leanh::lean_dec_ref(v_as_5249_);
    return v_res_5255_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_x_5257_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5258_: u8 = 0;
    let mut v_key_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5257_) == 0 {
                    v___x_5258_ = 0;
                    return v___x_5258_;
                } else {
                    v_key_5259_ = leanh::lean_ctor_get(v_x_5257_, 0);
                    v_tail_5260_ = leanh::lean_ctor_get(v_x_5257_, 2);
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
    mut v_a_5263_: *mut leanh::LeanObject,
    mut v_x_5264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5265_: u8 = 0;
    let mut v_r_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5263_, v_x_5264_);
    leanh::lean_dec(v_x_5264_);
    leanh::lean_dec(v_a_5263_);
    v_r_5266_ = leanh::lean_box((v_res_5265_) as usize);
    return v_r_5266_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u64 = 0;
    v___x_5267_ = leanh::lean_unsigned_to_nat(1723);
    v___x_5268_ = lean_uint64_of_nat(v___x_5267_);
    return v___x_5268_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(
    mut v_m_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: u64 = 0;
    let mut v_hash_5289_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5271_ = leanh::lean_ctor_get(v_m_5269_, 1);
                v___x_5272_ = lean_array_get_size(v_buckets_5271_);
                if leanh::lean_obj_tag(v_a_5270_) == 0 {
                    v___x_5288_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5274_ = v___x_5288_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5289_ = leanh::lean_ctor_get_uint64(
                        v_a_5270_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_5290_: *mut leanh::LeanObject,
    mut v_a_5291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5292_: u8 = 0;
    let mut v_r_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5290_, v_a_5291_);
    leanh::lean_dec(v_a_5291_);
    leanh::lean_dec_ref(v_m_5290_);
    v_r_5293_ = leanh::lean_box((v_res_5292_) as usize);
    return v_r_5293_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(
    mut v_x_5294_: *mut leanh::LeanObject,
    mut v_x_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u64 = 0;
    let mut v_hash_5323_: u64 = 0;
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5295_) == 0 {
                    return v_x_5294_;
                } else {
                    v_key_5296_ = leanh::lean_ctor_get(v_x_5295_, 0);
                    v_value_5297_ = leanh::lean_ctor_get(v_x_5295_, 1);
                    v_tail_5298_ = leanh::lean_ctor_get(v_x_5295_, 2);
                    v_isSharedCheck_5324_ = (!leanh::lean_is_exclusive(v_x_5295_)) as u8;
                    if v_isSharedCheck_5324_ == 0 {
                        v___x_5300_ = v_x_5295_;
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5298_);
                        leanh::lean_inc(v_value_5297_);
                        leanh::lean_inc(v_key_5296_);
                        leanh::lean_dec(v_x_5295_);
                        v___x_5300_ = leanh::lean_box(0);
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5302_ = lean_array_get_size(v_x_5294_);
                if leanh::lean_obj_tag(v_key_5296_) == 0 {
                    v___x_5322_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5304_ = v___x_5322_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5323_ = leanh::lean_ctor_get_uint64(
                        v_key_5296_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_5316_);
                if v_isShared_5301_ == 0 {
                    leanh::lean_ctor_set(v___x_5300_, 2, v___x_5316_);
                    v___x_5318_ = v___x_5300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_key_5296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_value_5297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 2, v___x_5316_);
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
    mut v_i_5325_: *mut leanh::LeanObject,
    mut v_source_5326_: *mut leanh::LeanObject,
    mut v_target_5327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: u8 = 0;
    let mut v_es_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5328_ = lean_array_get_size(v_source_5326_);
                v___x_5329_ = lean_nat_dec_lt(v_i_5325_, v___x_5328_);
                if v___x_5329_ == 0 {
                    leanh::lean_dec_ref(v_source_5326_);
                    leanh::lean_dec(v_i_5325_);
                    return v_target_5327_;
                } else {
                    v_es_5330_ = lean_array_fget(v_source_5326_, v_i_5325_);
                    v___x_5331_ = leanh::lean_box(0);
                    v_source_5332_ = lean_array_fset(v_source_5326_, v_i_5325_, v___x_5331_);
                    v_target_5333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_5327_, v_es_5330_);
                    v___x_5334_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5335_ = lean_nat_add(v_i_5325_, v___x_5334_);
                    leanh::lean_dec(v_i_5325_);
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
    mut v_data_5337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5338_ = lean_array_get_size(v_data_5337_);
    v___x_5339_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5340_ = lean_nat_mul(v___x_5338_, v___x_5339_);
    v___x_5341_ = leanh::lean_unsigned_to_nat(0);
    v___x_5342_ = leanh::lean_box(0);
    v___x_5343_ = lean_mk_array(v_nbuckets_5340_, v___x_5342_);
    v___x_5344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_5341_, v_data_5337_, v___x_5343_);
    return v___x_5344_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(
    mut v_m_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
    mut v_b_5347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v_val_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_unused_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: u64 = 0;
    let mut v_hash_5390_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5348_ = leanh::lean_ctor_get(v_m_5345_, 0);
                v_buckets_5349_ = leanh::lean_ctor_get(v_m_5345_, 1);
                v___x_5350_ = lean_array_get_size(v_buckets_5349_);
                if leanh::lean_obj_tag(v_a_5346_) == 0 {
                    v___x_5389_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5352_ = v___x_5389_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5390_ = leanh::lean_ctor_get_uint64(
                        v_a_5346_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_inc_ref(v_buckets_5349_);
                    leanh::lean_inc(v_size_5348_);
                    v_isSharedCheck_5386_ = (!leanh::lean_is_exclusive(v_m_5345_)) as u8;
                    if v_isSharedCheck_5386_ == 0 {
                        v_unused_5387_ = leanh::lean_ctor_get(v_m_5345_, 1);
                        leanh::lean_dec(v_unused_5387_);
                        v_unused_5388_ = leanh::lean_ctor_get(v_m_5345_, 0);
                        leanh::lean_dec(v_unused_5388_);
                        v___x_5367_ = v_m_5345_;
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_5345_);
                        v___x_5367_ = leanh::lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_5347_);
                    leanh::lean_dec(v_a_5346_);
                    return v_m_5345_;
                }
            }
            2 => {
                v___x_5369_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_5370_ = lean_nat_add(v_size_5348_, v___x_5369_);
                leanh::lean_dec(v_size_5348_);
                leanh::lean_inc(v_bkt_5364_);
                v___x_5371_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5371_, 0, v_a_5346_);
                leanh::lean_ctor_set(v___x_5371_, 1, v_b_5347_);
                leanh::lean_ctor_set(v___x_5371_, 2, v_bkt_5364_);
                v_buckets_x27_5372_ = lean_array_uset(v_buckets_5349_, v___x_5363_, v___x_5371_);
                v___x_5373_ = leanh::lean_unsigned_to_nat(4);
                v___x_5374_ = lean_nat_mul(v_size_x27_5370_, v___x_5373_);
                v___x_5375_ = leanh::lean_unsigned_to_nat(3);
                v___x_5376_ = lean_nat_div(v___x_5374_, v___x_5375_);
                leanh::lean_dec(v___x_5374_);
                v___x_5377_ = lean_array_get_size(v_buckets_x27_5372_);
                v___x_5378_ = lean_nat_dec_le(v___x_5376_, v___x_5377_);
                leanh::lean_dec(v___x_5376_);
                if v___x_5378_ == 0 {
                    v_val_5379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_5372_);
                    if v_isShared_5368_ == 0 {
                        leanh::lean_ctor_set(v___x_5367_, 1, v_val_5379_);
                        leanh::lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5381_ = v___x_5367_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_size_x27_5370_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_val_5379_);
                        v___x_5381_ = v_reuseFailAlloc_5382_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_5368_ == 0 {
                        leanh::lean_ctor_set(v___x_5367_, 1, v_buckets_x27_5372_);
                        leanh::lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5384_ = v___x_5367_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_size_x27_5370_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 1, v_buckets_x27_5372_);
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
    mut v___x_5391_: *mut leanh::LeanObject,
    mut v_as_5392_: *mut leanh::LeanObject,
    mut v_sz_5393_: usize,
    mut v_i_5394_: usize,
    mut v_b_5395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: usize = 0;
    let mut v___x_5400_: usize = 0;
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v_fst_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v_array_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v_a_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5433_: usize = 0;
    let mut v___x_5434_: usize = 0;
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_edits_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_unused_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5488_: u8 = 0;
    let mut v_unused_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5490_: u8 = 0;
    let mut v_unused_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_unused_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5496_: u8 = 0;
    let mut v_unused_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5402_ = lean_usize_dec_lt(v_i_5394_, v_sz_5393_);
                if v___x_5402_ == 0 {
                    leanh::lean_dec_ref(v___x_5391_);
                    v___x_5403_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5403_, 0, v_b_5395_);
                    return v___x_5403_;
                } else {
                    v_snd_5404_ = leanh::lean_ctor_get(v_b_5395_, 1);
                    leanh::lean_inc(v_snd_5404_);
                    v_snd_5405_ = leanh::lean_ctor_get(v_snd_5404_, 1);
                    leanh::lean_inc(v_snd_5405_);
                    v_fst_5406_ = leanh::lean_ctor_get(v_b_5395_, 0);
                    v_isSharedCheck_5496_ = (!leanh::lean_is_exclusive(v_b_5395_)) as u8;
                    if v_isSharedCheck_5496_ == 0 {
                        v_unused_5497_ = leanh::lean_ctor_get(v_b_5395_, 1);
                        leanh::lean_dec(v_unused_5497_);
                        v___x_5408_ = v_b_5395_;
                        v_isShared_5409_ = v_isSharedCheck_5496_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_5406_);
                        leanh::lean_dec(v_b_5395_);
                        v___x_5408_ = leanh::lean_box(0);
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
                v_fst_5410_ = leanh::lean_ctor_get(v_snd_5404_, 0);
                v_isSharedCheck_5494_ = (!leanh::lean_is_exclusive(v_snd_5404_)) as u8;
                if v_isSharedCheck_5494_ == 0 {
                    v_unused_5495_ = leanh::lean_ctor_get(v_snd_5404_, 1);
                    leanh::lean_dec(v_unused_5495_);
                    v___x_5412_ = v_snd_5404_;
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5410_);
                    leanh::lean_dec(v_snd_5404_);
                    v___x_5412_ = leanh::lean_box(0);
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_5414_ = leanh::lean_ctor_get(v_snd_5405_, 0);
                v_start_5415_ = leanh::lean_ctor_get(v_snd_5405_, 1);
                v_stop_5416_ = leanh::lean_ctor_get(v_snd_5405_, 2);
                v___x_5417_ = lean_nat_dec_lt(v_start_5415_, v_stop_5416_);
                if v___x_5417_ == 0 {
                    leanh::lean_dec_ref(v___x_5391_);
                    if v_isShared_5413_ == 0 {
                        v___x_5419_ = v___x_5412_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5424_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_fst_5410_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_snd_5405_);
                        v___x_5419_ = v_reuseFailAlloc_5424_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_5416_);
                    leanh::lean_inc(v_start_5415_);
                    leanh::lean_inc_ref(v_array_5414_);
                    v_isSharedCheck_5490_ = (!leanh::lean_is_exclusive(v_snd_5405_)) as u8;
                    if v_isSharedCheck_5490_ == 0 {
                        v_unused_5491_ = leanh::lean_ctor_get(v_snd_5405_, 2);
                        leanh::lean_dec(v_unused_5491_);
                        v_unused_5492_ = leanh::lean_ctor_get(v_snd_5405_, 1);
                        leanh::lean_dec(v_unused_5492_);
                        v_unused_5493_ = leanh::lean_ctor_get(v_snd_5405_, 0);
                        leanh::lean_dec(v_unused_5493_);
                        v___x_5426_ = v_snd_5405_;
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_5405_);
                        v___x_5426_ = leanh::lean_box(0);
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5409_ == 0 {
                    leanh::lean_ctor_set(v___x_5408_, 1, v___x_5419_);
                    v___x_5421_ = v___x_5408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_fst_5406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5419_);
                    v___x_5421_ = v_reuseFailAlloc_5423_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5422_, 0, v___x_5421_);
                return v___x_5422_;
            }
            6 => {
                v_a_5428_ = lean_array_uget_borrowed(v_as_5392_, v_i_5394_);
                v___x_5429_ = lean_array_fget_borrowed(v_array_5414_, v_start_5415_);
                v___x_5430_ = leanh::lean_box(0);
                v___x_5431_ = leanh::lean_box(0);
                v___x_5432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                v_sz_5433_ = lean_array_size(v___x_5429_);
                v___x_5434_ = 0usize;
                leanh::lean_inc(v_a_5428_);
                v___x_5435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5428_, v___x_5429_, v_sz_5433_, v___x_5434_, v___x_5432_);
                v_fst_5436_ = leanh::lean_ctor_get(v___x_5435_, 0);
                v_isSharedCheck_5488_ = (!leanh::lean_is_exclusive(v___x_5435_)) as u8;
                if v_isSharedCheck_5488_ == 0 {
                    v_unused_5489_ = leanh::lean_ctor_get(v___x_5435_, 1);
                    leanh::lean_dec(v_unused_5489_);
                    v___x_5438_ = v___x_5435_;
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5436_);
                    leanh::lean_dec(v___x_5435_);
                    v___x_5438_ = leanh::lean_box(0);
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5440_ = leanh::lean_unsigned_to_nat(1);
                v___x_5441_ = lean_nat_add(v_start_5415_, v___x_5440_);
                leanh::lean_dec(v_start_5415_);
                if v_isShared_5427_ == 0 {
                    leanh::lean_ctor_set(v___x_5426_, 1, v___x_5441_);
                    v___x_5443_ = v___x_5426_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5487_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_array_5414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_stop_5416_);
                    v___x_5443_ = v_reuseFailAlloc_5487_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_fst_5436_) == 0 {
                    leanh::lean_del_object(v___x_5408_);
                    state = 9;
                    continue;
                } else {
                    v_val_5451_ = leanh::lean_ctor_get(v_fst_5436_, 0);
                    leanh::lean_inc(v_val_5451_);
                    leanh::lean_dec_ref_known(v_fst_5436_, 1);
                    if leanh::lean_obj_tag(v_val_5451_) == 1 {
                        leanh::lean_del_object(v___x_5438_);
                        leanh::lean_del_object(v___x_5412_);
                        v_val_5452_ = leanh::lean_ctor_get(v_val_5451_, 0);
                        leanh::lean_inc(v_val_5452_);
                        leanh::lean_dec_ref_known(v_val_5451_, 1);
                        v_ctx_5453_ = leanh::lean_ctor_get(v_a_5428_, 1);
                        v_toCommandContextInfo_5454_ = leanh::lean_ctor_get(v_ctx_5453_, 0);
                        v_module_5455_ = leanh::lean_ctor_get(v_val_5452_, 0);
                        leanh::lean_inc(v_module_5455_);
                        v_decl_5456_ = leanh::lean_ctor_get(v_val_5452_, 1);
                        leanh::lean_inc(v_decl_5456_);
                        leanh::lean_dec(v_val_5452_);
                        v_determineInsertion_5457_ = leanh::lean_ctor_get(v_a_5428_, 2);
                        v_env_5458_ = leanh::lean_ctor_get(v_toCommandContextInfo_5454_, 0);
                        v___x_5459_ = l_Lean_Environment_mainModule(v_env_5458_);
                        v___x_5460_ = lean_name_eq(v_module_5455_, v___x_5459_);
                        leanh::lean_dec(v___x_5459_);
                        if v___x_5460_ == 0 {
                            leanh::lean_inc_ref(v_determineInsertion_5457_);
                            v___x_5461_ = leanh::lean_apply_1(
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
                            leanh::lean_dec(v_decl_5456_);
                            leanh::lean_dec(v_module_5455_);
                            if v_isShared_5409_ == 0 {
                                leanh::lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                                leanh::lean_ctor_set(v___x_5408_, 0, v_fst_5410_);
                                v___x_5484_ = v___x_5408_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_5486_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_fst_5410_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5486_, 1, v___x_5443_);
                                v___x_5484_ = v_reuseFailAlloc_5486_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_5451_);
                        leanh::lean_del_object(v___x_5408_);
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5439_ == 0 {
                    leanh::lean_ctor_set(v___x_5438_, 1, v___x_5443_);
                    leanh::lean_ctor_set(v___x_5438_, 0, v_fst_5410_);
                    v___x_5446_ = v___x_5438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5450_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_fst_5410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 1, v___x_5443_);
                    v___x_5446_ = v_reuseFailAlloc_5450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5413_ == 0 {
                    leanh::lean_ctor_set(v___x_5412_, 1, v___x_5446_);
                    leanh::lean_ctor_set(v___x_5412_, 0, v_fst_5406_);
                    v___x_5448_ = v___x_5412_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5446_);
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
                v_edit_5464_ = leanh::lean_ctor_get(v___x_5461_, 1);
                v_isSharedCheck_5476_ = (!leanh::lean_is_exclusive(v___x_5461_)) as u8;
                if v_isSharedCheck_5476_ == 0 {
                    v_unused_5477_ = leanh::lean_ctor_get(v___x_5461_, 0);
                    leanh::lean_dec(v_unused_5477_);
                    v___x_5466_ = v___x_5461_;
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_edit_5464_);
                    leanh::lean_dec(v___x_5461_);
                    v___x_5466_ = leanh::lean_box(0);
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5468_ = lean_array_push(v_edits_5463_, v_edit_5464_);
                v___x_5469_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_5410_, v_module_5455_, v___x_5431_);
                if v_isShared_5409_ == 0 {
                    leanh::lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                    leanh::lean_ctor_set(v___x_5408_, 0, v___x_5469_);
                    v___x_5471_ = v___x_5408_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 1, v___x_5443_);
                    v___x_5471_ = v_reuseFailAlloc_5475_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5467_ == 0 {
                    leanh::lean_ctor_set(v___x_5466_, 1, v___x_5471_);
                    leanh::lean_ctor_set(v___x_5466_, 0, v___x_5468_);
                    v___x_5473_ = v___x_5466_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5471_);
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
                leanh::lean_inc(v_module_5455_);
                leanh::lean_inc_ref(v_ctx_5453_);
                v___x_5479_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_5453_, v_module_5455_);
                leanh::lean_inc_ref(v___x_5391_);
                v___x_5480_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5480_, 0, v___x_5391_);
                leanh::lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                leanh::lean_ctor_set(v___x_5480_, 2, v___x_5430_);
                leanh::lean_ctor_set(v___x_5480_, 3, v___x_5430_);
                v___x_5481_ = lean_array_push(v_fst_5406_, v___x_5480_);
                v_edits_5463_ = v___x_5481_;
                state = 12;
                continue;
            }
            17 => {
                v___x_5485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5485_, 0, v_fst_5406_);
                leanh::lean_ctor_set(v___x_5485_, 1, v___x_5484_);
                v_a_5398_ = v___x_5485_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(
    mut v___x_5498_: *mut leanh::LeanObject,
    mut v_as_5499_: *mut leanh::LeanObject,
    mut v_sz_5500_: *mut leanh::LeanObject,
    mut v_i_5501_: *mut leanh::LeanObject,
    mut v_b_5502_: *mut leanh::LeanObject,
    mut v___y_5503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5504_: usize = 0;
    let mut v_i_boxed_5505_: usize = 0;
    let mut v_res_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5504_ = leanh::lean_unbox_usize(v_sz_5500_);
    leanh::lean_dec(v_sz_5500_);
    v_i_boxed_5505_ = leanh::lean_unbox_usize(v_i_5501_);
    leanh::lean_dec(v_i_5501_);
    v_res_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5498_, v_as_5499_, v_sz_boxed_5504_, v_i_boxed_5505_, v_b_5502_);
    leanh::lean_dec_ref(v_as_5499_);
    return v_res_5506_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(
    mut v___x_5507_: *mut leanh::LeanObject,
    mut v_as_5508_: *mut leanh::LeanObject,
    mut v_i_5509_: usize,
    mut v_stop_5510_: usize,
    mut v_b_5511_: *mut leanh::LeanObject,
    mut v___y_5512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: usize = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5519_ = lean_usize_dec_eq(v_i_5509_, v_stop_5510_);
                if v___x_5519_ == 0 {
                    v___x_5520_ = lean_array_uget_borrowed(v_as_5508_, v_i_5509_);
                    v_stop_5521_ = leanh::lean_ctor_get(v___x_5520_, 1);
                    leanh::lean_inc(v_stop_5521_);
                    leanh::lean_inc_ref(v___x_5507_);
                    v___x_5522_ = l_Lean_Server_FileWorker_computeQueries(
                        v___x_5507_,
                        v_stop_5521_,
                        v___y_5512_,
                    );
                    if leanh::lean_obj_tag(v___x_5522_) == 0 {
                        v_a_5523_ = leanh::lean_ctor_get(v___x_5522_, 0);
                        leanh::lean_inc(v_a_5523_);
                        leanh::lean_dec_ref_known(v___x_5522_, 1);
                        v___x_5524_ = l_Array_append___redArg(v_b_5511_, v_a_5523_);
                        leanh::lean_dec(v_a_5523_);
                        v_a_5515_ = v___x_5524_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_5511_);
                        if leanh::lean_obj_tag(v___x_5522_) == 0 {
                            v_a_5525_ = leanh::lean_ctor_get(v___x_5522_, 0);
                            leanh::lean_inc(v_a_5525_);
                            leanh::lean_dec_ref_known(v___x_5522_, 1);
                            v_a_5515_ = v_a_5525_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_5507_);
                            return v___x_5522_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5507_);
                    v___x_5526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5526_, 0, v_b_5511_);
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
    mut v___x_5527_: *mut leanh::LeanObject,
    mut v_as_5528_: *mut leanh::LeanObject,
    mut v_i_5529_: *mut leanh::LeanObject,
    mut v_stop_5530_: *mut leanh::LeanObject,
    mut v_b_5531_: *mut leanh::LeanObject,
    mut v___y_5532_: *mut leanh::LeanObject,
    mut v___y_5533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5534_: usize = 0;
    let mut v_stop_boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5534_ = leanh::lean_unbox_usize(v_i_5529_);
    leanh::lean_dec(v_i_5529_);
    v_stop_boxed_5535_ = leanh::lean_unbox_usize(v_stop_5530_);
    leanh::lean_dec(v_stop_5530_);
    v_res_5536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_5527_, v_as_5528_, v_i_boxed_5534_, v_stop_boxed_5535_, v_b_5531_, v___y_5532_);
    leanh::lean_dec_ref(v___y_5532_);
    leanh::lean_dec_ref(v_as_5528_);
    return v_res_5536_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5537_ = leanh::lean_box(0);
    v___x_5538_ = leanh::lean_unsigned_to_nat(16);
    v___x_5539_ = lean_mk_array(v___x_5538_, v___x_5537_);
    return v___x_5539_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
    mut v_id_5542_: *mut leanh::LeanObject,
    mut v_action_5543_: *mut leanh::LeanObject,
    mut v_unknownIdentifierRanges_5544_: *mut leanh::LeanObject,
    mut v_a_5545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_doc_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: usize = 0;
    let mut v___y_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: usize = 0;
    let mut v___y_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v_fst_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v_toWorkDoneProgressParams_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_x3f_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreferred_x3f_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disabled_x3f_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_command_x3f_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_unused_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_unused_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_a_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut v_toEditableDocumentCore_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSnap_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5620_: usize = 0;
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut v_unused_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: u8 = 0;
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5547_ = leanh::lean_ctor_get(v_a_5545_, 1);
                v_toEditableDocumentCore_5610_ = leanh::lean_ctor_get(v_doc_5547_, 0);
                v_meta_5611_ = leanh::lean_ctor_get(v_toEditableDocumentCore_5610_, 0);
                v_initSnap_5612_ = leanh::lean_ctor_get(v_toEditableDocumentCore_5610_, 1);
                v_text_5613_ = leanh::lean_ctor_get(v_meta_5611_, 3);
                v___x_5665_ = leanh::lean_unsigned_to_nat(0);
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
                            leanh::lean_inc_ref(v_doc_5547_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5670_, v___x_5671_, v___x_5666_, v_a_5545_);
                            v___y_5655_ = v___x_5672_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_5673_ = 0usize;
                        v___x_5674_ = lean_usize_of_nat(v___x_5667_);
                        leanh::lean_inc_ref(v_doc_5547_);
                        v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5673_, v___x_5674_, v___x_5666_, v_a_5545_);
                        v___y_5655_ = v___x_5675_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_5554_);
                v___x_5555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5555_, 0, v___y_5554_);
                leanh::lean_ctor_set(v___x_5555_, 1, v___y_5554_);
                v___x_5556_ = lean_mk_empty_array_with_capacity(v___y_5552_);
                v___x_5557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once), _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
                leanh::lean_inc(v___y_5552_);
                v___x_5558_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5558_, 0, v___y_5552_);
                leanh::lean_ctor_set(v___x_5558_, 1, v___x_5557_);
                v___x_5559_ = lean_array_get_size(v___y_5553_);
                v___x_5560_ = l_Array_toSubarray___redArg(v___y_5553_, v___y_5552_, v___x_5559_);
                v___x_5561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5561_, 0, v___x_5558_);
                leanh::lean_ctor_set(v___x_5561_, 1, v___x_5560_);
                v___x_5562_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5562_, 0, v___x_5556_);
                leanh::lean_ctor_set(v___x_5562_, 1, v___x_5561_);
                v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5555_, v___y_5550_, v___y_5549_, v___y_5551_, v___x_5562_);
                leanh::lean_dec_ref(v___y_5550_);
                if leanh::lean_obj_tag(v___x_5563_) == 0 {
                    v_a_5564_ = leanh::lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5601_ = (!leanh::lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5601_ == 0 {
                        v___x_5566_ = v___x_5563_;
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5564_);
                        leanh::lean_dec(v___x_5563_);
                        v___x_5566_ = leanh::lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_action_5543_);
                    v_a_5602_ = leanh::lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5609_ = (!leanh::lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v___x_5563_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5602_);
                        leanh::lean_dec(v___x_5563_);
                        v___x_5604_ = leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5568_ = leanh::lean_ctor_get(v_a_5564_, 0);
                v_isSharedCheck_5599_ = (!leanh::lean_is_exclusive(v_a_5564_)) as u8;
                if v_isSharedCheck_5599_ == 0 {
                    v_unused_5600_ = leanh::lean_ctor_get(v_a_5564_, 1);
                    leanh::lean_dec(v_unused_5600_);
                    v___x_5570_ = v_a_5564_;
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5568_);
                    leanh::lean_dec(v_a_5564_);
                    v___x_5570_ = leanh::lean_box(0);
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toWorkDoneProgressParams_5572_ = leanh::lean_ctor_get(v_action_5543_, 0);
                v_toPartialResultParams_5573_ = leanh::lean_ctor_get(v_action_5543_, 1);
                v_title_5574_ = leanh::lean_ctor_get(v_action_5543_, 2);
                v_kind_x3f_5575_ = leanh::lean_ctor_get(v_action_5543_, 3);
                v_diagnostics_x3f_5576_ = leanh::lean_ctor_get(v_action_5543_, 4);
                v_isPreferred_x3f_5577_ = leanh::lean_ctor_get(v_action_5543_, 5);
                v_disabled_x3f_5578_ = leanh::lean_ctor_get(v_action_5543_, 6);
                v_command_x3f_5579_ = leanh::lean_ctor_get(v_action_5543_, 8);
                v_data_x3f_5580_ = leanh::lean_ctor_get(v_action_5543_, 9);
                v_isSharedCheck_5597_ = (!leanh::lean_is_exclusive(v_action_5543_)) as u8;
                if v_isSharedCheck_5597_ == 0 {
                    v_unused_5598_ = leanh::lean_ctor_get(v_action_5543_, 7);
                    leanh::lean_dec(v_unused_5598_);
                    v___x_5582_ = v_action_5543_;
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_data_x3f_5580_);
                    leanh::lean_inc(v_command_x3f_5579_);
                    leanh::lean_inc(v_disabled_x3f_5578_);
                    leanh::lean_inc(v_isPreferred_x3f_5577_);
                    leanh::lean_inc(v_diagnostics_x3f_5576_);
                    leanh::lean_inc(v_kind_x3f_5575_);
                    leanh::lean_inc(v_title_5574_);
                    leanh::lean_inc(v_toPartialResultParams_5573_);
                    leanh::lean_inc(v_toWorkDoneProgressParams_5572_);
                    leanh::lean_dec(v_action_5543_);
                    v___x_5582_ = leanh::lean_box(0);
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_doc_5547_);
                v___x_5584_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_5547_);
                if v_isShared_5571_ == 0 {
                    leanh::lean_ctor_set(v___x_5570_, 1, v_fst_5568_);
                    leanh::lean_ctor_set(v___x_5570_, 0, v___x_5584_);
                    v___x_5586_ = v___x_5570_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_fst_5568_);
                    v___x_5586_ = v_reuseFailAlloc_5596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5587_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_5586_);
                v___x_5588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5588_, 0, v___x_5587_);
                if v_isShared_5583_ == 0 {
                    leanh::lean_ctor_set(v___x_5582_, 7, v___x_5588_);
                    v___x_5590_ = v___x_5582_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5595_,
                        0,
                        v_toWorkDoneProgressParams_5572_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5595_,
                        1,
                        v_toPartialResultParams_5573_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_title_5574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 3, v_kind_x3f_5575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 4, v_diagnostics_x3f_5576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 5, v_isPreferred_x3f_5577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 6, v_disabled_x3f_5578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 7, v___x_5588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 8, v_command_x3f_5579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 9, v_data_x3f_5580_);
                    v___x_5590_ = v_reuseFailAlloc_5595_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5591_, 0, v___x_5590_);
                if v_isShared_5567_ == 0 {
                    leanh::lean_ctor_set(v___x_5566_, 0, v___x_5591_);
                    v___x_5593_ = v___x_5566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5591_);
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
                    v_reuseFailAlloc_5608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
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
                v___x_5617_ = leanh::lean_unsigned_to_nat(0);
                v___x_5618_ = lean_nat_dec_eq(v___x_5616_, v___x_5617_);
                if v___x_5618_ == 0 {
                    v___x_5619_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5620_ = lean_array_size(v_a_5615_);
                    v___x_5621_ = 0usize;
                    leanh::lean_inc_ref(v_a_5615_);
                    v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5620_, v___x_5621_, v_a_5615_);
                    v___x_5623_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5623_, 0, v_id_5542_);
                    leanh::lean_ctor_set(v___x_5623_, 1, v___x_5622_);
                    v___x_5624_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5619_, v___x_5623_, v_a_5545_);
                    v_a_5625_ = leanh::lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5651_ = (!leanh::lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5651_ == 0 {
                        v___x_5627_ = v___x_5624_;
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5625_);
                        leanh::lean_dec(v___x_5624_);
                        v___x_5627_ = leanh::lean_box(0);
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_5615_);
                    leanh::lean_dec_ref(v_action_5543_);
                    leanh::lean_dec(v_id_5542_);
                    v___x_5652_ = leanh::lean_box(0);
                    v___x_5653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5653_, 0, v___x_5652_);
                    return v___x_5653_;
                }
            }
            11 => {
                v___x_5629_ = lean_task_get_own(v_a_5625_);
                if leanh::lean_obj_tag(v___x_5629_) == 0 {
                    leanh::lean_del_object(v___x_5627_);
                    v_response_5630_ = leanh::lean_ctor_get(v___x_5629_, 0);
                    leanh::lean_inc(v_response_5630_);
                    leanh::lean_dec_ref_known(v___x_5629_, 1);
                    v_stx_5631_ = leanh::lean_ctor_get(v_initSnap_5612_, 3);
                    v___x_5632_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5631_, v___x_5618_);
                    if leanh::lean_obj_tag(v___x_5632_) == 0 {
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
                        v_val_5634_ = leanh::lean_ctor_get(v___x_5632_, 0);
                        leanh::lean_inc(v_val_5634_);
                        leanh::lean_dec_ref_known(v___x_5632_, 1);
                        leanh::lean_inc_ref(v_text_5613_);
                        v___x_5635_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5613_, v_val_5634_);
                        leanh::lean_dec(v_val_5634_);
                        v_line_5636_ = leanh::lean_ctor_get(v___x_5635_, 0);
                        v_isSharedCheck_5645_ =
                            (!leanh::lean_is_exclusive(v___x_5635_)) as u8;
                        if v_isSharedCheck_5645_ == 0 {
                            v_unused_5646_ = leanh::lean_ctor_get(v___x_5635_, 1);
                            leanh::lean_dec(v_unused_5646_);
                            v___x_5638_ = v___x_5635_;
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_line_5636_);
                            leanh::lean_dec(v___x_5635_);
                            v___x_5638_ = leanh::lean_box(0);
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5629_);
                    leanh::lean_dec_ref(v_a_5615_);
                    leanh::lean_dec_ref(v_action_5543_);
                    v___x_5647_ = leanh::lean_box(0);
                    if v_isShared_5628_ == 0 {
                        leanh::lean_ctor_set(v___x_5627_, 0, v___x_5647_);
                        v___x_5649_ = v___x_5627_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5647_);
                        v___x_5649_ = v_reuseFailAlloc_5650_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5640_ = leanh::lean_unsigned_to_nat(1);
                v___x_5641_ = lean_nat_add(v_line_5636_, v___x_5640_);
                leanh::lean_dec(v_line_5636_);
                if v_isShared_5639_ == 0 {
                    leanh::lean_ctor_set(v___x_5638_, 1, v___x_5617_);
                    leanh::lean_ctor_set(v___x_5638_, 0, v___x_5641_);
                    v___x_5643_ = v___x_5638_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5644_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 1, v___x_5617_);
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
                if leanh::lean_obj_tag(v___y_5655_) == 0 {
                    v_a_5656_ = leanh::lean_ctor_get(v___y_5655_, 0);
                    leanh::lean_inc(v_a_5656_);
                    leanh::lean_dec_ref_known(v___y_5655_, 1);
                    v_a_5615_ = v_a_5656_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_action_5543_);
                    leanh::lean_dec(v_id_5542_);
                    v_a_5657_ = leanh::lean_ctor_get(v___y_5655_, 0);
                    v_isSharedCheck_5664_ = (!leanh::lean_is_exclusive(v___y_5655_)) as u8;
                    if v_isSharedCheck_5664_ == 0 {
                        v___x_5659_ = v___y_5655_;
                        v_isShared_5660_ = v_isSharedCheck_5664_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5657_);
                        leanh::lean_dec(v___y_5655_);
                        v___x_5659_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_a_5657_);
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
    mut v_id_5676_: *mut leanh::LeanObject,
    mut v_action_5677_: *mut leanh::LeanObject,
    mut v_unknownIdentifierRanges_5678_: *mut leanh::LeanObject,
    mut v_a_5679_: *mut leanh::LeanObject,
    mut v_a_5680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5681_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
        v_id_5676_,
        v_action_5677_,
        v_unknownIdentifierRanges_5678_,
        v_a_5679_,
    );
    leanh::lean_dec_ref(v_a_5679_);
    leanh::lean_dec_ref(v_unknownIdentifierRanges_5678_);
    return v_res_5681_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(
    mut v_00_u03b2_5682_: *mut leanh::LeanObject,
    mut v_m_5683_: *mut leanh::LeanObject,
    mut v_a_5684_: *mut leanh::LeanObject,
    mut v_b_5685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_5683_, v_a_5684_, v_b_5685_);
    return v___x_5686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(
    mut v_00_u03b2_5687_: *mut leanh::LeanObject,
    mut v_m_5688_: *mut leanh::LeanObject,
    mut v_a_5689_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5690_: u8 = 0;
    v___x_5690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5688_, v_a_5689_);
    return v___x_5690_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(
    mut v_00_u03b2_5691_: *mut leanh::LeanObject,
    mut v_m_5692_: *mut leanh::LeanObject,
    mut v_a_5693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5694_: u8 = 0;
    let mut v_r_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5694_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_5691_, v_m_5692_, v_a_5693_);
    leanh::lean_dec(v_a_5693_);
    leanh::lean_dec_ref(v_m_5692_);
    v_r_5695_ = leanh::lean_box((v_res_5694_) as usize);
    return v_r_5695_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(
    mut v___x_5696_: *mut leanh::LeanObject,
    mut v_as_5697_: *mut leanh::LeanObject,
    mut v_sz_5698_: usize,
    mut v_i_5699_: usize,
    mut v_b_5700_: *mut leanh::LeanObject,
    mut v___y_5701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5696_, v_as_5697_, v_sz_5698_, v_i_5699_, v_b_5700_);
    return v___x_5703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(
    mut v___x_5704_: *mut leanh::LeanObject,
    mut v_as_5705_: *mut leanh::LeanObject,
    mut v_sz_5706_: *mut leanh::LeanObject,
    mut v_i_5707_: *mut leanh::LeanObject,
    mut v_b_5708_: *mut leanh::LeanObject,
    mut v___y_5709_: *mut leanh::LeanObject,
    mut v___y_5710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5711_: usize = 0;
    let mut v_i_boxed_5712_: usize = 0;
    let mut v_res_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5711_ = leanh::lean_unbox_usize(v_sz_5706_);
    leanh::lean_dec(v_sz_5706_);
    v_i_boxed_5712_ = leanh::lean_unbox_usize(v_i_5707_);
    leanh::lean_dec(v_i_5707_);
    v_res_5713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_5704_, v_as_5705_, v_sz_boxed_5711_, v_i_boxed_5712_, v_b_5708_, v___y_5709_);
    leanh::lean_dec_ref(v___y_5709_);
    leanh::lean_dec_ref(v_as_5705_);
    return v_res_5713_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(
    mut v_00_u03b2_5714_: *mut leanh::LeanObject,
    mut v_a_5715_: *mut leanh::LeanObject,
    mut v_x_5716_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5717_: u8 = 0;
    v___x_5717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5715_, v_x_5716_);
    return v___x_5717_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_5718_: *mut leanh::LeanObject,
    mut v_a_5719_: *mut leanh::LeanObject,
    mut v_x_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5721_: u8 = 0;
    let mut v_r_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_5718_, v_a_5719_, v_x_5720_);
    leanh::lean_dec(v_x_5720_);
    leanh::lean_dec(v_a_5719_);
    v_r_5722_ = leanh::lean_box((v_res_5721_) as usize);
    return v_r_5722_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(
    mut v_00_u03b2_5723_: *mut leanh::LeanObject,
    mut v_data_5724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_5724_);
    return v___x_5725_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5726_: *mut leanh::LeanObject,
    mut v_i_5727_: *mut leanh::LeanObject,
    mut v_source_5728_: *mut leanh::LeanObject,
    mut v_target_5729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_5727_, v_source_5728_, v_target_5729_);
    return v___x_5730_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(
    mut v_00_u03b2_5731_: *mut leanh::LeanObject,
    mut v_x_5732_: *mut leanh::LeanObject,
    mut v_x_5733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_5732_, v_x_5733_);
    return v___x_5734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(
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
pub unsafe fn initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
}