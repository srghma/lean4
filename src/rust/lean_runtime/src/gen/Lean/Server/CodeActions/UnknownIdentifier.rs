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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value:
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
    m_fun: l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value:
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
    m_fun: l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value
) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_computeQueries___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Server_FileWorker_computeQueries___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_computeQueries___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value:
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
        97, 108, 108, 85, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101,
        114, 115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value:
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
            l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value
        ) as *mut LeanObject,
        2250887845330408536 as *mut LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
) as *mut LeanObject;
pub static mut l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value:
    LeanStringObject<19> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value:
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
            l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value
        ) as *mut LeanObject,
        16966433945472317273 as *mut LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Server_FileWorker_importUnknownIdentifiersProvider: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value:
    LeanStringObject<43> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 98, 108, 105, 99, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 101, 116, 97, 32, 0]};
static mut l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value) as *mut LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 115, 101, 114, 118, 101, 114, 32, 114, 101, 113, 117, 101, 115, 116, 32, 114, 101, 115, 112, 111, 110, 115, 101, 58, 32, 0]};
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 104, 97, 110, 103, 101, 32, 116, 111, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 102, 114, 111, 109, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value:
    LeanStringObject<19> = LeanStringObject {
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
        36, 47, 108, 101, 97, 110, 47, 113, 117, 101, 114, 121, 77, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value:
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
    m_fun: l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value:
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
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value
)
    as *mut LeanObject;
pub static l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value
)
    as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(
    mut v_r1_2868_: *mut LeanObject,
    mut v_r2_2869_: *mut LeanObject,
) -> u8 {
    let mut v_start_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    v_start_2870_ = lean_ctor_get(v_r1_2868_, 0);
    v_stop_2871_ = lean_ctor_get(v_r1_2868_, 1);
    v_start_2872_ = lean_ctor_get(v_r2_2869_, 0);
    v_stop_2873_ = lean_ctor_get(v_r2_2869_, 1);
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
    mut v_r1_2883_: *mut LeanObject,
    mut v_r2_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2885_: u8 = 0;
    let mut v_r_2886_: *mut LeanObject = core::ptr::null_mut();
    v_res_2885_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_r1_2883_, v_r2_2884_);
    lean_dec_ref(v_r2_2884_);
    lean_dec_ref(v_r1_2883_);
    v_r_2886_ = lean_box((v_res_2885_) as usize);
    return v_r_2886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(
    mut v_k_2887_: *mut LeanObject,
    mut v_t_2888_: *mut LeanObject,
) -> u8 {
    let mut v_k_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2888_) == 0 {
                    v_k_2889_ = lean_ctor_get(v_t_2888_, 1);
                    v_l_2890_ = lean_ctor_get(v_t_2888_, 3);
                    v_r_2891_ = lean_ctor_get(v_t_2888_, 4);
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
    mut v_k_2897_: *mut LeanObject,
    mut v_t_2898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_2897_, v_t_2898_);
    lean_dec(v_t_2898_);
    lean_dec_ref(v_k_2897_);
    v_r_2900_ = lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(
    mut v_k_2901_: *mut LeanObject,
    mut v_v_2902_: *mut LeanObject,
    mut v_t_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v_impl_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_size_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_unused_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v_k_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v_unused_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_unused_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v_size_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_unused_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_unused_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v_k_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_unused_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_unused_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v_unused_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2903_) == 0 {
                    v_size_2904_ = lean_ctor_get(v_t_2903_, 0);
                    v_k_2905_ = lean_ctor_get(v_t_2903_, 1);
                    v_v_2906_ = lean_ctor_get(v_t_2903_, 2);
                    v_l_2907_ = lean_ctor_get(v_t_2903_, 3);
                    v_r_2908_ = lean_ctor_get(v_t_2903_, 4);
                    v_isSharedCheck_3188_ = (!lean_is_exclusive(v_t_2903_)) as u8;
                    if v_isSharedCheck_3188_ == 0 {
                        v___x_2910_ = v_t_2903_;
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2908_);
                        lean_inc(v_l_2907_);
                        lean_inc(v_v_2906_);
                        lean_inc(v_k_2905_);
                        lean_inc(v_size_2904_);
                        lean_dec(v_t_2903_);
                        v___x_2910_ = lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3189_ = lean_unsigned_to_nat(1);
                    v___x_3190_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3190_, 0, v___x_3189_);
                    lean_ctor_set(v___x_3190_, 1, v_k_2901_);
                    lean_ctor_set(v___x_3190_, 2, v_v_2902_);
                    lean_ctor_set(v___x_3190_, 3, v_t_2903_);
                    lean_ctor_set(v___x_3190_, 4, v_t_2903_);
                    return v___x_3190_;
                }
            }
            1 => {
                v___x_2912_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_2901_, v_k_2905_);
                match v___x_2912_ {
                    0 => {
                        lean_dec(v_size_2904_);
                        v_impl_2913_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_l_2907_);
                        v___x_2914_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_2908_) == 0 {
                            v_size_2915_ = lean_ctor_get(v_r_2908_, 0);
                            v_size_2916_ = lean_ctor_get(v_impl_2913_, 0);
                            lean_inc(v_size_2916_);
                            v_k_2917_ = lean_ctor_get(v_impl_2913_, 1);
                            lean_inc(v_k_2917_);
                            v_v_2918_ = lean_ctor_get(v_impl_2913_, 2);
                            lean_inc(v_v_2918_);
                            v_l_2919_ = lean_ctor_get(v_impl_2913_, 3);
                            lean_inc(v_l_2919_);
                            v_r_2920_ = lean_ctor_get(v_impl_2913_, 4);
                            lean_inc(v_r_2920_);
                            v___x_2921_ = lean_unsigned_to_nat(3);
                            v___x_2922_ = lean_nat_mul(v___x_2921_, v_size_2915_);
                            v___x_2923_ = lean_nat_dec_lt(v___x_2922_, v_size_2916_);
                            lean_dec(v___x_2922_);
                            if v___x_2923_ == 0 {
                                lean_dec(v_r_2920_);
                                lean_dec(v_l_2919_);
                                lean_dec(v_v_2918_);
                                lean_dec(v_k_2917_);
                                v___x_2924_ = lean_nat_add(v___x_2914_, v_size_2916_);
                                lean_dec(v_size_2916_);
                                v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2915_);
                                lean_dec(v___x_2924_);
                                if v_isShared_2911_ == 0 {
                                    lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                    lean_ctor_set(v___x_2910_, 0, v___x_2925_);
                                    v___x_2927_ = v___x_2910_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
                                    lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2905_);
                                    lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2906_);
                                    lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_impl_2913_);
                                    lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_r_2908_);
                                    v___x_2927_ = v_reuseFailAlloc_2928_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2994_ = (!lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_2994_ == 0 {
                                    v_unused_2995_ = lean_ctor_get(v_impl_2913_, 4);
                                    lean_dec(v_unused_2995_);
                                    v_unused_2996_ = lean_ctor_get(v_impl_2913_, 3);
                                    lean_dec(v_unused_2996_);
                                    v_unused_2997_ = lean_ctor_get(v_impl_2913_, 2);
                                    lean_dec(v_unused_2997_);
                                    v_unused_2998_ = lean_ctor_get(v_impl_2913_, 1);
                                    lean_dec(v_unused_2998_);
                                    v_unused_2999_ = lean_ctor_get(v_impl_2913_, 0);
                                    lean_dec(v_unused_2999_);
                                    v___x_2930_ = v_impl_2913_;
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2913_);
                                    v___x_2930_ = lean_box(0);
                                    v_isShared_2931_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3000_ = lean_ctor_get(v_impl_2913_, 3);
                            lean_inc(v_l_3000_);
                            if lean_obj_tag(v_l_3000_) == 0 {
                                v_r_3001_ = lean_ctor_get(v_impl_2913_, 4);
                                v_k_3002_ = lean_ctor_get(v_impl_2913_, 1);
                                v_v_3003_ = lean_ctor_get(v_impl_2913_, 2);
                                v_isSharedCheck_3014_ = (!lean_is_exclusive(v_impl_2913_)) as u8;
                                if v_isSharedCheck_3014_ == 0 {
                                    v_unused_3015_ = lean_ctor_get(v_impl_2913_, 3);
                                    lean_dec(v_unused_3015_);
                                    v_unused_3016_ = lean_ctor_get(v_impl_2913_, 0);
                                    lean_dec(v_unused_3016_);
                                    v___x_3005_ = v_impl_2913_;
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_3001_);
                                    lean_inc(v_v_3003_);
                                    lean_inc(v_k_3002_);
                                    lean_dec(v_impl_2913_);
                                    v___x_3005_ = lean_box(0);
                                    v_isShared_3006_ = v_isSharedCheck_3014_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3017_ = lean_ctor_get(v_impl_2913_, 4);
                                lean_inc(v_r_3017_);
                                if lean_obj_tag(v_r_3017_) == 0 {
                                    v_k_3018_ = lean_ctor_get(v_impl_2913_, 1);
                                    v_v_3019_ = lean_ctor_get(v_impl_2913_, 2);
                                    v_isSharedCheck_3042_ =
                                        (!lean_is_exclusive(v_impl_2913_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v_unused_3043_ = lean_ctor_get(v_impl_2913_, 4);
                                        lean_dec(v_unused_3043_);
                                        v_unused_3044_ = lean_ctor_get(v_impl_2913_, 3);
                                        lean_dec(v_unused_3044_);
                                        v_unused_3045_ = lean_ctor_get(v_impl_2913_, 0);
                                        lean_dec(v_unused_3045_);
                                        v___x_3021_ = v_impl_2913_;
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3019_);
                                        lean_inc(v_k_3018_);
                                        lean_dec(v_impl_2913_);
                                        v___x_3021_ = lean_box(0);
                                        v_isShared_3022_ = v_isSharedCheck_3042_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3046_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        lean_ctor_set(v___x_2910_, 4, v_r_3017_);
                                        lean_ctor_set(v___x_2910_, 3, v_impl_2913_);
                                        lean_ctor_set(v___x_2910_, 0, v___x_3046_);
                                        v___x_3048_ = v___x_2910_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
                                        lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_k_2905_);
                                        lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_v_2906_);
                                        lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_impl_2913_);
                                        lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_r_3017_);
                                        v___x_3048_ = v_reuseFailAlloc_3049_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_2906_);
                        lean_dec(v_k_2905_);
                        if v_isShared_2911_ == 0 {
                            lean_ctor_set(v___x_2910_, 2, v_v_2902_);
                            lean_ctor_set(v___x_2910_, 1, v_k_2901_);
                            v___x_3051_ = v___x_2910_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_size_2904_);
                            lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_k_2901_);
                            lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_v_2902_);
                            lean_ctor_set(v_reuseFailAlloc_3052_, 3, v_l_2907_);
                            lean_ctor_set(v_reuseFailAlloc_3052_, 4, v_r_2908_);
                            v___x_3051_ = v_reuseFailAlloc_3052_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_2904_);
                        v_impl_3053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_2901_, v_v_2902_, v_r_2908_);
                        v___x_3054_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_2907_) == 0 {
                            v_size_3055_ = lean_ctor_get(v_l_2907_, 0);
                            v_size_3056_ = lean_ctor_get(v_impl_3053_, 0);
                            lean_inc(v_size_3056_);
                            v_k_3057_ = lean_ctor_get(v_impl_3053_, 1);
                            lean_inc(v_k_3057_);
                            v_v_3058_ = lean_ctor_get(v_impl_3053_, 2);
                            lean_inc(v_v_3058_);
                            v_l_3059_ = lean_ctor_get(v_impl_3053_, 3);
                            lean_inc(v_l_3059_);
                            v_r_3060_ = lean_ctor_get(v_impl_3053_, 4);
                            lean_inc(v_r_3060_);
                            v___x_3061_ = lean_unsigned_to_nat(3);
                            v___x_3062_ = lean_nat_mul(v___x_3061_, v_size_3055_);
                            v___x_3063_ = lean_nat_dec_lt(v___x_3062_, v_size_3056_);
                            lean_dec(v___x_3062_);
                            if v___x_3063_ == 0 {
                                lean_dec(v_r_3060_);
                                lean_dec(v_l_3059_);
                                lean_dec(v_v_3058_);
                                lean_dec(v_k_3057_);
                                v___x_3064_ = lean_nat_add(v___x_3054_, v_size_3055_);
                                v___x_3065_ = lean_nat_add(v___x_3064_, v_size_3056_);
                                lean_dec(v_size_3056_);
                                lean_dec(v___x_3064_);
                                if v_isShared_2911_ == 0 {
                                    lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                    lean_ctor_set(v___x_2910_, 0, v___x_3065_);
                                    v___x_3067_ = v___x_2910_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
                                    lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_k_2905_);
                                    lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_v_2906_);
                                    lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_l_2907_);
                                    lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_impl_3053_);
                                    v___x_3067_ = v_reuseFailAlloc_3068_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3132_ = (!lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3132_ == 0 {
                                    v_unused_3133_ = lean_ctor_get(v_impl_3053_, 4);
                                    lean_dec(v_unused_3133_);
                                    v_unused_3134_ = lean_ctor_get(v_impl_3053_, 3);
                                    lean_dec(v_unused_3134_);
                                    v_unused_3135_ = lean_ctor_get(v_impl_3053_, 2);
                                    lean_dec(v_unused_3135_);
                                    v_unused_3136_ = lean_ctor_get(v_impl_3053_, 1);
                                    lean_dec(v_unused_3136_);
                                    v_unused_3137_ = lean_ctor_get(v_impl_3053_, 0);
                                    lean_dec(v_unused_3137_);
                                    v___x_3070_ = v_impl_3053_;
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3053_);
                                    v___x_3070_ = lean_box(0);
                                    v_isShared_3071_ = v_isSharedCheck_3132_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3138_ = lean_ctor_get(v_impl_3053_, 3);
                            lean_inc(v_l_3138_);
                            if lean_obj_tag(v_l_3138_) == 0 {
                                v_r_3139_ = lean_ctor_get(v_impl_3053_, 4);
                                v_k_3140_ = lean_ctor_get(v_impl_3053_, 1);
                                v_v_3141_ = lean_ctor_get(v_impl_3053_, 2);
                                v_isSharedCheck_3164_ = (!lean_is_exclusive(v_impl_3053_)) as u8;
                                if v_isSharedCheck_3164_ == 0 {
                                    v_unused_3165_ = lean_ctor_get(v_impl_3053_, 3);
                                    lean_dec(v_unused_3165_);
                                    v_unused_3166_ = lean_ctor_get(v_impl_3053_, 0);
                                    lean_dec(v_unused_3166_);
                                    v___x_3143_ = v_impl_3053_;
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_3139_);
                                    lean_inc(v_v_3141_);
                                    lean_inc(v_k_3140_);
                                    lean_dec(v_impl_3053_);
                                    v___x_3143_ = lean_box(0);
                                    v_isShared_3144_ = v_isSharedCheck_3164_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3167_ = lean_ctor_get(v_impl_3053_, 4);
                                lean_inc(v_r_3167_);
                                if lean_obj_tag(v_r_3167_) == 0 {
                                    v_k_3168_ = lean_ctor_get(v_impl_3053_, 1);
                                    v_v_3169_ = lean_ctor_get(v_impl_3053_, 2);
                                    v_isSharedCheck_3180_ =
                                        (!lean_is_exclusive(v_impl_3053_)) as u8;
                                    if v_isSharedCheck_3180_ == 0 {
                                        v_unused_3181_ = lean_ctor_get(v_impl_3053_, 4);
                                        lean_dec(v_unused_3181_);
                                        v_unused_3182_ = lean_ctor_get(v_impl_3053_, 3);
                                        lean_dec(v_unused_3182_);
                                        v_unused_3183_ = lean_ctor_get(v_impl_3053_, 0);
                                        lean_dec(v_unused_3183_);
                                        v___x_3171_ = v_impl_3053_;
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3169_);
                                        lean_inc(v_k_3168_);
                                        lean_dec(v_impl_3053_);
                                        v___x_3171_ = lean_box(0);
                                        v_isShared_3172_ = v_isSharedCheck_3180_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3184_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2911_ == 0 {
                                        lean_ctor_set(v___x_2910_, 4, v_impl_3053_);
                                        lean_ctor_set(v___x_2910_, 3, v_r_3167_);
                                        lean_ctor_set(v___x_2910_, 0, v___x_3184_);
                                        v___x_3186_ = v___x_2910_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3184_);
                                        lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_k_2905_);
                                        lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_v_2906_);
                                        lean_ctor_set(v_reuseFailAlloc_3187_, 3, v_r_3167_);
                                        lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_impl_3053_);
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
                v_size_2932_ = lean_ctor_get(v_l_2919_, 0);
                v_size_2933_ = lean_ctor_get(v_r_2920_, 0);
                v_k_2934_ = lean_ctor_get(v_r_2920_, 1);
                v_v_2935_ = lean_ctor_get(v_r_2920_, 2);
                v_l_2936_ = lean_ctor_get(v_r_2920_, 3);
                v_r_2937_ = lean_ctor_get(v_r_2920_, 4);
                v___x_2938_ = lean_unsigned_to_nat(2);
                v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
                v___x_2940_ = lean_nat_dec_lt(v_size_2933_, v___x_2939_);
                lean_dec(v___x_2939_);
                if v___x_2940_ == 0 {
                    lean_inc(v_r_2937_);
                    lean_inc(v_l_2936_);
                    lean_inc(v_v_2935_);
                    lean_inc(v_k_2934_);
                    v_isSharedCheck_2969_ = (!lean_is_exclusive(v_r_2920_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v_unused_2970_ = lean_ctor_get(v_r_2920_, 4);
                        lean_dec(v_unused_2970_);
                        v_unused_2971_ = lean_ctor_get(v_r_2920_, 3);
                        lean_dec(v_unused_2971_);
                        v_unused_2972_ = lean_ctor_get(v_r_2920_, 2);
                        lean_dec(v_unused_2972_);
                        v_unused_2973_ = lean_ctor_get(v_r_2920_, 1);
                        lean_dec(v_unused_2973_);
                        v_unused_2974_ = lean_ctor_get(v_r_2920_, 0);
                        lean_dec(v_unused_2974_);
                        v___x_2942_ = v_r_2920_;
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_2920_);
                        v___x_2942_ = lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2910_);
                    v___x_2975_ = lean_nat_add(v___x_2914_, v_size_2916_);
                    lean_dec(v_size_2916_);
                    v___x_2976_ = lean_nat_add(v___x_2975_, v_size_2915_);
                    lean_dec(v___x_2975_);
                    v___x_2977_ = lean_nat_add(v___x_2914_, v_size_2915_);
                    v___x_2978_ = lean_nat_add(v___x_2977_, v_size_2933_);
                    lean_dec(v___x_2977_);
                    lean_inc_ref(v_r_2908_);
                    if v_isShared_2931_ == 0 {
                        lean_ctor_set(v___x_2930_, 4, v_r_2908_);
                        lean_ctor_set(v___x_2930_, 3, v_r_2920_);
                        lean_ctor_set(v___x_2930_, 2, v_v_2906_);
                        lean_ctor_set(v___x_2930_, 1, v_k_2905_);
                        lean_ctor_set(v___x_2930_, 0, v___x_2978_);
                        v___x_2980_ = v___x_2930_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2978_);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2905_);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2906_);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_r_2920_);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_r_2908_);
                        v___x_2980_ = v_reuseFailAlloc_2993_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2944_ = lean_nat_add(v___x_2914_, v_size_2916_);
                lean_dec(v_size_2916_);
                v___x_2945_ = lean_nat_add(v___x_2944_, v_size_2915_);
                lean_dec(v___x_2944_);
                v___x_2957_ = lean_nat_add(v___x_2914_, v_size_2932_);
                if lean_obj_tag(v_l_2936_) == 0 {
                    v_size_2967_ = lean_ctor_get(v_l_2936_, 0);
                    lean_inc(v_size_2967_);
                    v___y_2959_ = v_size_2967_;
                    state = 8;
                    continue;
                } else {
                    v___x_2968_ = lean_unsigned_to_nat(0);
                    v___y_2959_ = v___x_2968_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2950_ = lean_nat_add(v___y_2948_, v___y_2949_);
                lean_dec(v___y_2949_);
                lean_dec(v___y_2948_);
                if v_isShared_2943_ == 0 {
                    lean_ctor_set(v___x_2942_, 4, v_r_2908_);
                    lean_ctor_set(v___x_2942_, 3, v_r_2937_);
                    lean_ctor_set(v___x_2942_, 2, v_v_2906_);
                    lean_ctor_set(v___x_2942_, 1, v_k_2905_);
                    lean_ctor_set(v___x_2942_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_r_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_r_2908_);
                    v___x_2952_ = v_reuseFailAlloc_2956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2931_ == 0 {
                    lean_ctor_set(v___x_2930_, 4, v___x_2952_);
                    lean_ctor_set(v___x_2930_, 3, v___y_2947_);
                    lean_ctor_set(v___x_2930_, 2, v_v_2935_);
                    lean_ctor_set(v___x_2930_, 1, v_k_2934_);
                    lean_ctor_set(v___x_2930_, 0, v___x_2945_);
                    v___x_2954_ = v___x_2930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2945_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2934_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2935_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 3, v___y_2947_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 4, v___x_2952_);
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
                lean_dec(v___y_2959_);
                lean_dec(v___x_2957_);
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v_l_2936_);
                    lean_ctor_set(v___x_2910_, 3, v_l_2919_);
                    lean_ctor_set(v___x_2910_, 2, v_v_2918_);
                    lean_ctor_set(v___x_2910_, 1, v_k_2917_);
                    lean_ctor_set(v___x_2910_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2910_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2960_);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_l_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_l_2936_);
                    v___x_2962_ = v_reuseFailAlloc_2966_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2963_ = lean_nat_add(v___x_2914_, v_size_2915_);
                if lean_obj_tag(v_r_2937_) == 0 {
                    v_size_2964_ = lean_ctor_get(v_r_2937_, 0);
                    lean_inc(v_size_2964_);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v_size_2964_;
                    state = 5;
                    continue;
                } else {
                    v___x_2965_ = lean_unsigned_to_nat(0);
                    v___y_2947_ = v___x_2962_;
                    v___y_2948_ = v___x_2963_;
                    v___y_2949_ = v___x_2965_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2987_ = (!lean_is_exclusive(v_r_2908_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v_unused_2988_ = lean_ctor_get(v_r_2908_, 4);
                    lean_dec(v_unused_2988_);
                    v_unused_2989_ = lean_ctor_get(v_r_2908_, 3);
                    lean_dec(v_unused_2989_);
                    v_unused_2990_ = lean_ctor_get(v_r_2908_, 2);
                    lean_dec(v_unused_2990_);
                    v_unused_2991_ = lean_ctor_get(v_r_2908_, 1);
                    lean_dec(v_unused_2991_);
                    v_unused_2992_ = lean_ctor_get(v_r_2908_, 0);
                    lean_dec(v_unused_2992_);
                    v___x_2982_ = v_r_2908_;
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_2908_);
                    v___x_2982_ = lean_box(0);
                    v_isShared_2983_ = v_isSharedCheck_2987_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2983_ == 0 {
                    lean_ctor_set(v___x_2982_, 4, v___x_2980_);
                    lean_ctor_set(v___x_2982_, 3, v_l_2919_);
                    lean_ctor_set(v___x_2982_, 2, v_v_2918_);
                    lean_ctor_set(v___x_2982_, 1, v_k_2917_);
                    lean_ctor_set(v___x_2982_, 0, v___x_2976_);
                    v___x_2985_ = v___x_2982_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2976_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_l_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2985_;
            }
            13 => {
                v___x_3007_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3001_);
                if v_isShared_3006_ == 0 {
                    lean_ctor_set(v___x_3005_, 3, v_r_3001_);
                    lean_ctor_set(v___x_3005_, 2, v_v_2906_);
                    lean_ctor_set(v___x_3005_, 1, v_k_2905_);
                    lean_ctor_set(v___x_3005_, 0, v___x_2914_);
                    v___x_3009_ = v___x_3005_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2914_);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_r_3001_);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_r_3001_);
                    v___x_3009_ = v_reuseFailAlloc_3013_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v___x_3009_);
                    lean_ctor_set(v___x_2910_, 3, v_l_3000_);
                    lean_ctor_set(v___x_2910_, 2, v_v_3003_);
                    lean_ctor_set(v___x_2910_, 1, v_k_3002_);
                    lean_ctor_set(v___x_2910_, 0, v___x_3007_);
                    v___x_3011_ = v___x_2910_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3007_);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_3002_);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_3003_);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___x_3009_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3011_;
            }
            16 => {
                v_k_3023_ = lean_ctor_get(v_r_3017_, 1);
                v_v_3024_ = lean_ctor_get(v_r_3017_, 2);
                v_isSharedCheck_3038_ = (!lean_is_exclusive(v_r_3017_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v_unused_3039_ = lean_ctor_get(v_r_3017_, 4);
                    lean_dec(v_unused_3039_);
                    v_unused_3040_ = lean_ctor_get(v_r_3017_, 3);
                    lean_dec(v_unused_3040_);
                    v_unused_3041_ = lean_ctor_get(v_r_3017_, 0);
                    lean_dec(v_unused_3041_);
                    v___x_3026_ = v_r_3017_;
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_3024_);
                    lean_inc(v_k_3023_);
                    lean_dec(v_r_3017_);
                    v___x_3026_ = lean_box(0);
                    v_isShared_3027_ = v_isSharedCheck_3038_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3028_ = lean_unsigned_to_nat(3);
                if v_isShared_3027_ == 0 {
                    lean_ctor_set(v___x_3026_, 4, v_l_3000_);
                    lean_ctor_set(v___x_3026_, 3, v_l_3000_);
                    lean_ctor_set(v___x_3026_, 2, v_v_3019_);
                    lean_ctor_set(v___x_3026_, 1, v_k_3018_);
                    lean_ctor_set(v___x_3026_, 0, v___x_2914_);
                    v___x_3030_ = v___x_3026_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_2914_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_k_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_v_3019_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_l_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_l_3000_);
                    v___x_3030_ = v_reuseFailAlloc_3037_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3022_ == 0 {
                    lean_ctor_set(v___x_3021_, 4, v_l_3000_);
                    lean_ctor_set(v___x_3021_, 2, v_v_2906_);
                    lean_ctor_set(v___x_3021_, 1, v_k_2905_);
                    lean_ctor_set(v___x_3021_, 0, v___x_2914_);
                    v___x_3032_ = v___x_3021_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2914_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_l_3000_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v___x_3032_);
                    lean_ctor_set(v___x_2910_, 3, v___x_3030_);
                    lean_ctor_set(v___x_2910_, 2, v_v_3024_);
                    lean_ctor_set(v___x_2910_, 1, v_k_3023_);
                    lean_ctor_set(v___x_2910_, 0, v___x_3028_);
                    v___x_3034_ = v___x_2910_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3028_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 3, v___x_3030_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 4, v___x_3032_);
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
                v_size_3072_ = lean_ctor_get(v_l_3059_, 0);
                v_k_3073_ = lean_ctor_get(v_l_3059_, 1);
                v_v_3074_ = lean_ctor_get(v_l_3059_, 2);
                v_l_3075_ = lean_ctor_get(v_l_3059_, 3);
                v_r_3076_ = lean_ctor_get(v_l_3059_, 4);
                v_size_3077_ = lean_ctor_get(v_r_3060_, 0);
                v___x_3078_ = lean_unsigned_to_nat(2);
                v___x_3079_ = lean_nat_mul(v___x_3078_, v_size_3077_);
                v___x_3080_ = lean_nat_dec_lt(v_size_3072_, v___x_3079_);
                lean_dec(v___x_3079_);
                if v___x_3080_ == 0 {
                    lean_inc(v_r_3076_);
                    lean_inc(v_l_3075_);
                    lean_inc(v_v_3074_);
                    lean_inc(v_k_3073_);
                    v_isSharedCheck_3108_ = (!lean_is_exclusive(v_l_3059_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v_unused_3109_ = lean_ctor_get(v_l_3059_, 4);
                        lean_dec(v_unused_3109_);
                        v_unused_3110_ = lean_ctor_get(v_l_3059_, 3);
                        lean_dec(v_unused_3110_);
                        v_unused_3111_ = lean_ctor_get(v_l_3059_, 2);
                        lean_dec(v_unused_3111_);
                        v_unused_3112_ = lean_ctor_get(v_l_3059_, 1);
                        lean_dec(v_unused_3112_);
                        v_unused_3113_ = lean_ctor_get(v_l_3059_, 0);
                        lean_dec(v_unused_3113_);
                        v___x_3082_ = v_l_3059_;
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_3059_);
                        v___x_3082_ = lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3108_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2910_);
                    v___x_3114_ = lean_nat_add(v___x_3054_, v_size_3055_);
                    v___x_3115_ = lean_nat_add(v___x_3114_, v_size_3056_);
                    lean_dec(v_size_3056_);
                    v___x_3116_ = lean_nat_add(v___x_3114_, v_size_3072_);
                    lean_dec(v___x_3114_);
                    lean_inc_ref(v_l_2907_);
                    if v_isShared_3071_ == 0 {
                        lean_ctor_set(v___x_3070_, 4, v_l_3059_);
                        lean_ctor_set(v___x_3070_, 3, v_l_2907_);
                        lean_ctor_set(v___x_3070_, 2, v_v_2906_);
                        lean_ctor_set(v___x_3070_, 1, v_k_2905_);
                        lean_ctor_set(v___x_3070_, 0, v___x_3116_);
                        v___x_3118_ = v___x_3070_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3116_);
                        lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_2905_);
                        lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_2906_);
                        lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_l_2907_);
                        lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3059_);
                        v___x_3118_ = v_reuseFailAlloc_3131_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3084_ = lean_nat_add(v___x_3054_, v_size_3055_);
                v___x_3085_ = lean_nat_add(v___x_3084_, v_size_3056_);
                lean_dec(v_size_3056_);
                if lean_obj_tag(v_l_3075_) == 0 {
                    v_size_3106_ = lean_ctor_get(v_l_3075_, 0);
                    lean_inc(v_size_3106_);
                    v___y_3098_ = v_size_3106_;
                    state = 29;
                    continue;
                } else {
                    v___x_3107_ = lean_unsigned_to_nat(0);
                    v___y_3098_ = v___x_3107_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3090_ = lean_nat_add(v___y_3087_, v___y_3089_);
                lean_dec(v___y_3089_);
                lean_dec(v___y_3087_);
                if v_isShared_3083_ == 0 {
                    lean_ctor_set(v___x_3082_, 4, v_r_3060_);
                    lean_ctor_set(v___x_3082_, 3, v_r_3076_);
                    lean_ctor_set(v___x_3082_, 2, v_v_3058_);
                    lean_ctor_set(v___x_3082_, 1, v_k_3057_);
                    lean_ctor_set(v___x_3082_, 0, v___x_3090_);
                    v___x_3092_ = v___x_3082_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3057_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3058_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_r_3076_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_r_3060_);
                    v___x_3092_ = v_reuseFailAlloc_3096_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3071_ == 0 {
                    lean_ctor_set(v___x_3070_, 4, v___x_3092_);
                    lean_ctor_set(v___x_3070_, 3, v___y_3088_);
                    lean_ctor_set(v___x_3070_, 2, v_v_3074_);
                    lean_ctor_set(v___x_3070_, 1, v_k_3073_);
                    lean_ctor_set(v___x_3070_, 0, v___x_3085_);
                    v___x_3094_ = v___x_3070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_k_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_v_3074_);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 3, v___y_3088_);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 4, v___x_3092_);
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
                lean_dec(v___y_3098_);
                lean_dec(v___x_3084_);
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v_l_3075_);
                    lean_ctor_set(v___x_2910_, 0, v___x_3099_);
                    v___x_3101_ = v___x_2910_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3099_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_l_2907_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_l_3075_);
                    v___x_3101_ = v_reuseFailAlloc_3105_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3102_ = lean_nat_add(v___x_3054_, v_size_3077_);
                if lean_obj_tag(v_r_3076_) == 0 {
                    v_size_3103_ = lean_ctor_get(v_r_3076_, 0);
                    lean_inc(v_size_3103_);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v_size_3103_;
                    state = 26;
                    continue;
                } else {
                    v___x_3104_ = lean_unsigned_to_nat(0);
                    v___y_3087_ = v___x_3102_;
                    v___y_3088_ = v___x_3101_;
                    v___y_3089_ = v___x_3104_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3125_ = (!lean_is_exclusive(v_l_2907_)) as u8;
                if v_isSharedCheck_3125_ == 0 {
                    v_unused_3126_ = lean_ctor_get(v_l_2907_, 4);
                    lean_dec(v_unused_3126_);
                    v_unused_3127_ = lean_ctor_get(v_l_2907_, 3);
                    lean_dec(v_unused_3127_);
                    v_unused_3128_ = lean_ctor_get(v_l_2907_, 2);
                    lean_dec(v_unused_3128_);
                    v_unused_3129_ = lean_ctor_get(v_l_2907_, 1);
                    lean_dec(v_unused_3129_);
                    v_unused_3130_ = lean_ctor_get(v_l_2907_, 0);
                    lean_dec(v_unused_3130_);
                    v___x_3120_ = v_l_2907_;
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_2907_);
                    v___x_3120_ = lean_box(0);
                    v_isShared_3121_ = v_isSharedCheck_3125_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3121_ == 0 {
                    lean_ctor_set(v___x_3120_, 4, v_r_3060_);
                    lean_ctor_set(v___x_3120_, 3, v___x_3118_);
                    lean_ctor_set(v___x_3120_, 2, v_v_3058_);
                    lean_ctor_set(v___x_3120_, 1, v_k_3057_);
                    lean_ctor_set(v___x_3120_, 0, v___x_3115_);
                    v___x_3123_ = v___x_3120_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3115_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_k_3057_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_v_3058_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___x_3118_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_r_3060_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3123_;
            }
            34 => {
                v_k_3145_ = lean_ctor_get(v_l_3138_, 1);
                v_v_3146_ = lean_ctor_get(v_l_3138_, 2);
                v_isSharedCheck_3160_ = (!lean_is_exclusive(v_l_3138_)) as u8;
                if v_isSharedCheck_3160_ == 0 {
                    v_unused_3161_ = lean_ctor_get(v_l_3138_, 4);
                    lean_dec(v_unused_3161_);
                    v_unused_3162_ = lean_ctor_get(v_l_3138_, 3);
                    lean_dec(v_unused_3162_);
                    v_unused_3163_ = lean_ctor_get(v_l_3138_, 0);
                    lean_dec(v_unused_3163_);
                    v___x_3148_ = v_l_3138_;
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_3146_);
                    lean_inc(v_k_3145_);
                    lean_dec(v_l_3138_);
                    v___x_3148_ = lean_box(0);
                    v_isShared_3149_ = v_isSharedCheck_3160_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3150_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3139_, 2);
                if v_isShared_3149_ == 0 {
                    lean_ctor_set(v___x_3148_, 4, v_r_3139_);
                    lean_ctor_set(v___x_3148_, 3, v_r_3139_);
                    lean_ctor_set(v___x_3148_, 2, v_v_2906_);
                    lean_ctor_set(v___x_3148_, 1, v_k_2905_);
                    lean_ctor_set(v___x_3148_, 0, v___x_3054_);
                    v___x_3152_ = v___x_3148_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3054_);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_r_3139_);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_r_3139_);
                    v___x_3152_ = v_reuseFailAlloc_3159_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_3139_);
                if v_isShared_3144_ == 0 {
                    lean_ctor_set(v___x_3143_, 3, v_r_3139_);
                    lean_ctor_set(v___x_3143_, 0, v___x_3054_);
                    v___x_3154_ = v___x_3143_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3054_);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_k_3140_);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_v_3141_);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_r_3139_);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_r_3139_);
                    v___x_3154_ = v_reuseFailAlloc_3158_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v___x_3154_);
                    lean_ctor_set(v___x_2910_, 3, v___x_3152_);
                    lean_ctor_set(v___x_2910_, 2, v_v_3146_);
                    lean_ctor_set(v___x_2910_, 1, v_k_3145_);
                    lean_ctor_set(v___x_2910_, 0, v___x_3150_);
                    v___x_3156_ = v___x_2910_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3150_);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_k_3145_);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_v_3146_);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 3, v___x_3152_);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 4, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3156_;
            }
            39 => {
                v___x_3173_ = lean_unsigned_to_nat(3);
                if v_isShared_3172_ == 0 {
                    lean_ctor_set(v___x_3171_, 4, v_l_3138_);
                    lean_ctor_set(v___x_3171_, 2, v_v_2906_);
                    lean_ctor_set(v___x_3171_, 1, v_k_2905_);
                    lean_ctor_set(v___x_3171_, 0, v___x_3054_);
                    v___x_3175_ = v___x_3171_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3054_);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_k_2905_);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_v_2906_);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_l_3138_);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_l_3138_);
                    v___x_3175_ = v_reuseFailAlloc_3179_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 4, v_r_3167_);
                    lean_ctor_set(v___x_2910_, 3, v___x_3175_);
                    lean_ctor_set(v___x_2910_, 2, v_v_3169_);
                    lean_ctor_set(v___x_2910_, 1, v_k_3168_);
                    lean_ctor_set(v___x_2910_, 0, v___x_3173_);
                    v___x_3177_ = v___x_2910_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_k_3168_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_v_3169_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 3, v___x_3175_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_r_3167_);
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
    mut v_a_3191_: *mut LeanObject,
    mut v_as_3192_: *mut LeanObject,
    mut v_i_3193_: usize,
    mut v_stop_3194_: usize,
) -> u8 {
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3202_: *mut LeanObject,
    mut v_as_3203_: *mut LeanObject,
    mut v_i_3204_: *mut LeanObject,
    mut v_stop_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3206_: usize = 0;
    let mut v_stop_boxed_3207_: usize = 0;
    let mut v_res_3208_: u8 = 0;
    let mut v_r_3209_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3206_ = lean_unbox_usize(v_i_3204_);
    lean_dec(v_i_3204_);
    v_stop_boxed_3207_ = lean_unbox_usize(v_stop_3205_);
    lean_dec(v_stop_3205_);
    v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_3202_, v_as_3203_, v_i_boxed_3206_, v_stop_boxed_3207_);
    lean_dec_ref(v_as_3203_);
    lean_dec_ref(v_a_3202_);
    v_r_3209_ = lean_box((v_res_3208_) as usize);
    return v_r_3209_;
}
pub unsafe fn l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
    mut v_as_3210_: *mut LeanObject,
    mut v_a_3211_: *mut LeanObject,
) -> u8 {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    v___x_3212_ = lean_unsigned_to_nat(0);
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
    mut v_as_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3220_: u8 = 0;
    let mut v_r_3221_: *mut LeanObject = core::ptr::null_mut();
    v_res_3220_ =
        l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(
            v_as_3218_, v_a_3219_,
        );
    lean_dec_ref(v_a_3219_);
    lean_dec_ref(v_as_3218_);
    v_r_3221_ = lean_box((v_res_3220_) as usize);
    return v_r_3221_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
    mut v_ctx_3222_: *mut LeanObject,
    mut v_i_3223_: *mut LeanObject,
    mut v_acc_3224_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_i_3223_) == 1 {
        let mut v_i_3225_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_3226_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expr_3227_: *mut LeanObject = core::ptr::null_mut();
        let mut v_stx_3228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: u8 = 0;
        let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
        v_i_3225_ = lean_ctor_get(v_i_3223_, 0);
        v_toElabInfo_3226_ = lean_ctor_get(v_i_3225_, 0);
        v_expr_3227_ = lean_ctor_get(v_i_3225_, 3);
        v_stx_3228_ = lean_ctor_get(v_toElabInfo_3226_, 1);
        v___x_3229_ = 1;
        v___x_3230_ = l_Lean_Syntax_getRange_x3f(v_stx_3228_, v___x_3229_);
        if lean_obj_tag(v___x_3230_) == 1 {
            let mut v_val_3231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: u8 = 0;
            v_val_3231_ = lean_ctor_get(v___x_3230_, 0);
            lean_inc(v_val_3231_);
            lean_dec_ref_known(v___x_3230_, 1);
            v___x_3232_ = l_Lean_Expr_isFVar(v_expr_3227_);
            if v___x_3232_ == 0 {
                lean_dec(v_val_3231_);
                return v_acc_3224_;
            } else {
                let mut v_autoImplicits_3233_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3234_: u8 = 0;
                v_autoImplicits_3233_ = lean_ctor_get(v_ctx_3222_, 2);
                v___x_3234_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(v_autoImplicits_3233_, v_expr_3227_);
                if v___x_3234_ == 0 {
                    lean_dec(v_val_3231_);
                    return v_acc_3224_;
                } else {
                    let mut v___x_3235_: u8 = 0;
                    v___x_3235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_val_3231_, v_acc_3224_);
                    if v___x_3235_ == 0 {
                        let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
                        v___x_3236_ = lean_box(0);
                        v___x_3237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_val_3231_, v___x_3236_, v_acc_3224_);
                        return v___x_3237_;
                    } else {
                        lean_dec(v_val_3231_);
                        return v_acc_3224_;
                    }
                }
            }
        } else {
            lean_dec(v___x_3230_);
            return v_acc_3224_;
        }
    } else {
        return v_acc_3224_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(
    mut v_ctx_3238_: *mut LeanObject,
    mut v_i_3239_: *mut LeanObject,
    mut v_acc_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3241_: *mut LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(
        v_ctx_3238_,
        v_i_3239_,
        v_acc_3240_,
    );
    lean_dec_ref(v_i_3239_);
    lean_dec_ref(v_ctx_3238_);
    return v_res_3241_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(
    mut v_x_3242_: *mut LeanObject,
) -> u8 {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    v___x_3243_ = l_Lean_unknownIdentifierMessageTag;
    v___x_3244_ = lean_name_eq(v_x_3242_, v___x_3243_);
    return v___x_3244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed(
    mut v_x_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3246_: u8 = 0;
    let mut v_r_3247_: *mut LeanObject = core::ptr::null_mut();
    v_res_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(v_x_3245_);
    lean_dec(v_x_3245_);
    v_r_3247_ = lean_box((v_res_3246_) as usize);
    return v_r_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(
    mut v_text_3249_: *mut LeanObject,
    mut v_requestedRange_3250_: *mut LeanObject,
    mut v_as_3251_: *mut LeanObject,
    mut v_sz_3252_: usize,
    mut v_i_3253_: usize,
    mut v_b_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3256_: u8 = 0;
    let mut v_snd_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_a_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: usize = 0;
    let mut v___x_3272_: usize = 0;
    let mut v_reuseFailAlloc_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v_ranges_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut v_unused_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
                if v___x_3256_ == 0 {
                    return v_b_3254_;
                } else {
                    v_snd_3257_ = lean_ctor_get(v_b_3254_, 1);
                    v_isSharedCheck_3284_ = (!lean_is_exclusive(v_b_3254_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v_unused_3285_ = lean_ctor_get(v_b_3254_, 0);
                        lean_dec(v_unused_3285_);
                        v___x_3259_ = v_b_3254_;
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3257_);
                        lean_dec(v_b_3254_);
                        v___x_3259_ = lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3261_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
                v_pos_3262_ = lean_ctor_get(v_a_3261_, 1);
                v_endPos_3263_ = lean_ctor_get(v_a_3261_, 2);
                v_data_3264_ = lean_ctor_get(v_a_3261_, 4);
                v___f_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3266_ = lean_box(0);
                lean_inc(v_data_3264_);
                v___x_3275_ = l_Lean_MessageData_hasTag(v___f_3265_, v_data_3264_);
                if v___x_3275_ == 0 {
                    v_a_3268_ = v_snd_3257_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3262_);
                    v___x_3276_ = l_Lean_FileMap_ofPosition(v_text_3249_, v_pos_3262_);
                    if lean_obj_tag(v_endPos_3263_) == 0 {
                        lean_inc_ref(v_pos_3262_);
                        v___y_3278_ = v_pos_3262_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3283_ = lean_ctor_get(v_endPos_3263_, 0);
                        lean_inc(v_val_3283_);
                        v___y_3278_ = v_val_3283_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 1, v_a_3268_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3266_);
                    v___x_3270_ = v___x_3259_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3266_);
                    lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_a_3268_);
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
                v_msgRange_3280_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3280_, 0, v___x_3276_);
                lean_ctor_set(v_msgRange_3280_, 1, v___x_3279_);
                v___x_3281_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3280_,
                    v_requestedRange_3250_,
                    v___x_3275_,
                    v___x_3275_,
                );
                if v___x_3281_ == 0 {
                    lean_dec_ref_known(v_msgRange_3280_, 2);
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
    mut v_text_3286_: *mut LeanObject,
    mut v_requestedRange_3287_: *mut LeanObject,
    mut v_as_3288_: *mut LeanObject,
    mut v_sz_3289_: *mut LeanObject,
    mut v_i_3290_: *mut LeanObject,
    mut v_b_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3293_: usize = 0;
    let mut v_i_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3289_);
    lean_dec(v_sz_3289_);
    v_i_boxed_3294_ = lean_unbox_usize(v_i_3290_);
    lean_dec(v_i_3290_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_3286_, v_requestedRange_3287_, v_as_3288_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3291_);
    lean_dec_ref(v_as_3288_);
    lean_dec_ref(v_requestedRange_3287_);
    lean_dec_ref(v_text_3286_);
    return v_res_3295_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(
    mut v_text_3296_: *mut LeanObject,
    mut v_requestedRange_3297_: *mut LeanObject,
    mut v_as_3298_: *mut LeanObject,
    mut v_sz_3299_: usize,
    mut v_i_3300_: usize,
    mut v_b_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3303_: u8 = 0;
    let mut v_snd_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v_a_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: usize = 0;
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v_ranges_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_unused_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3303_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
                if v___x_3303_ == 0 {
                    return v_b_3301_;
                } else {
                    v_snd_3304_ = lean_ctor_get(v_b_3301_, 1);
                    v_isSharedCheck_3331_ = (!lean_is_exclusive(v_b_3301_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v_unused_3332_ = lean_ctor_get(v_b_3301_, 0);
                        lean_dec(v_unused_3332_);
                        v___x_3306_ = v_b_3301_;
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3304_);
                        lean_dec(v_b_3301_);
                        v___x_3306_ = lean_box(0);
                        v_isShared_3307_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3308_ = lean_array_uget_borrowed(v_as_3298_, v_i_3300_);
                v_pos_3309_ = lean_ctor_get(v_a_3308_, 1);
                v_endPos_3310_ = lean_ctor_get(v_a_3308_, 2);
                v_data_3311_ = lean_ctor_get(v_a_3308_, 4);
                v___f_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3313_ = lean_box(0);
                lean_inc(v_data_3311_);
                v___x_3322_ = l_Lean_MessageData_hasTag(v___f_3312_, v_data_3311_);
                if v___x_3322_ == 0 {
                    v_a_3315_ = v_snd_3304_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3309_);
                    v___x_3323_ = l_Lean_FileMap_ofPosition(v_text_3296_, v_pos_3309_);
                    if lean_obj_tag(v_endPos_3310_) == 0 {
                        lean_inc_ref(v_pos_3309_);
                        v___y_3325_ = v_pos_3309_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3330_ = lean_ctor_get(v_endPos_3310_, 0);
                        lean_inc(v_val_3330_);
                        v___y_3325_ = v_val_3330_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3307_ == 0 {
                    lean_ctor_set(v___x_3306_, 1, v_a_3315_);
                    lean_ctor_set(v___x_3306_, 0, v___x_3313_);
                    v___x_3317_ = v___x_3306_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3313_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_a_3315_);
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
                v_msgRange_3327_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3327_, 0, v___x_3323_);
                lean_ctor_set(v_msgRange_3327_, 1, v___x_3326_);
                v___x_3328_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3327_,
                    v_requestedRange_3297_,
                    v___x_3322_,
                    v___x_3322_,
                );
                if v___x_3328_ == 0 {
                    lean_dec_ref_known(v_msgRange_3327_, 2);
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
    mut v_text_3333_: *mut LeanObject,
    mut v_requestedRange_3334_: *mut LeanObject,
    mut v_as_3335_: *mut LeanObject,
    mut v_sz_3336_: *mut LeanObject,
    mut v_i_3337_: *mut LeanObject,
    mut v_b_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3340_: usize = 0;
    let mut v_i_boxed_3341_: usize = 0;
    let mut v_res_3342_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3340_ = lean_unbox_usize(v_sz_3336_);
    lean_dec(v_sz_3336_);
    v_i_boxed_3341_ = lean_unbox_usize(v_i_3337_);
    lean_dec(v_i_3337_);
    v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3333_, v_requestedRange_3334_, v_as_3335_, v_sz_boxed_3340_, v_i_boxed_3341_, v_b_3338_);
    lean_dec_ref(v_as_3335_);
    lean_dec_ref(v_requestedRange_3334_);
    lean_dec_ref(v_text_3333_);
    return v_res_3342_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(
    mut v_init_3343_: *mut LeanObject,
    mut v_text_3344_: *mut LeanObject,
    mut v_requestedRange_3345_: *mut LeanObject,
    mut v_n_3346_: *mut LeanObject,
    mut v_b_3347_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_n_3346_) == 0 {
        let mut v_cs_3349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3352_: usize = 0;
        let mut v___x_3353_: usize = 0;
        let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3355_: *mut LeanObject = core::ptr::null_mut();
        v_cs_3349_ = lean_ctor_get(v_n_3346_, 0);
        v___x_3350_ = lean_box(0);
        v___x_3351_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3351_, 0, v___x_3350_);
        lean_ctor_set(v___x_3351_, 1, v_b_3347_);
        v_sz_3352_ = lean_array_size(v_cs_3349_);
        v___x_3353_ = 0usize;
        v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3343_, v_text_3344_, v_requestedRange_3345_, v_cs_3349_, v_sz_3352_, v___x_3353_, v___x_3351_);
        v_fst_3355_ = lean_ctor_get(v___x_3354_, 0);
        lean_inc(v_fst_3355_);
        if lean_obj_tag(v_fst_3355_) == 0 {
            let mut v_snd_3356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3356_ = lean_ctor_get(v___x_3354_, 1);
            lean_inc(v_snd_3356_);
            lean_dec_ref(v___x_3354_);
            v___x_3357_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3357_, 0, v_snd_3356_);
            return v___x_3357_;
        } else {
            let mut v_val_3358_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3354_);
            v_val_3358_ = lean_ctor_get(v_fst_3355_, 0);
            lean_inc(v_val_3358_);
            lean_dec_ref_known(v_fst_3355_, 1);
            return v_val_3358_;
        }
    } else {
        let mut v_vs_3359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3362_: usize = 0;
        let mut v___x_3363_: usize = 0;
        let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3365_: *mut LeanObject = core::ptr::null_mut();
        v_vs_3359_ = lean_ctor_get(v_n_3346_, 0);
        v___x_3360_ = lean_box(0);
        v___x_3361_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3361_, 0, v___x_3360_);
        lean_ctor_set(v___x_3361_, 1, v_b_3347_);
        v_sz_3362_ = lean_array_size(v_vs_3359_);
        v___x_3363_ = 0usize;
        v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_3344_, v_requestedRange_3345_, v_vs_3359_, v_sz_3362_, v___x_3363_, v___x_3361_);
        v_fst_3365_ = lean_ctor_get(v___x_3364_, 0);
        lean_inc(v_fst_3365_);
        if lean_obj_tag(v_fst_3365_) == 0 {
            let mut v_snd_3366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3366_ = lean_ctor_get(v___x_3364_, 1);
            lean_inc(v_snd_3366_);
            lean_dec_ref(v___x_3364_);
            v___x_3367_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3367_, 0, v_snd_3366_);
            return v___x_3367_;
        } else {
            let mut v_val_3368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3364_);
            v_val_3368_ = lean_ctor_get(v_fst_3365_, 0);
            lean_inc(v_val_3368_);
            lean_dec_ref_known(v_fst_3365_, 1);
            return v_val_3368_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(
    mut v_init_3369_: *mut LeanObject,
    mut v_text_3370_: *mut LeanObject,
    mut v_requestedRange_3371_: *mut LeanObject,
    mut v_as_3372_: *mut LeanObject,
    mut v_sz_3373_: usize,
    mut v_i_3374_: usize,
    mut v_b_3375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3377_: u8 = 0;
    let mut v_snd_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: usize = 0;
    let mut v___x_3393_: usize = 0;
    let mut v_reuseFailAlloc_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v_unused_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3377_ = lean_usize_dec_lt(v_i_3374_, v_sz_3373_);
                if v___x_3377_ == 0 {
                    return v_b_3375_;
                } else {
                    v_snd_3378_ = lean_ctor_get(v_b_3375_, 1);
                    v_isSharedCheck_3396_ = (!lean_is_exclusive(v_b_3375_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v_unused_3397_ = lean_ctor_get(v_b_3375_, 0);
                        lean_dec(v_unused_3397_);
                        v___x_3380_ = v_b_3375_;
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3378_);
                        lean_dec(v_b_3375_);
                        v___x_3380_ = lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3382_ = lean_array_uget_borrowed(v_as_3372_, v_i_3374_);
                lean_inc(v_snd_3378_);
                v___x_3383_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3369_, v_text_3370_, v_requestedRange_3371_, v_a_3382_, v_snd_3378_);
                if lean_obj_tag(v___x_3383_) == 0 {
                    v___x_3384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3384_, 0, v___x_3383_);
                    if v_isShared_3381_ == 0 {
                        lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3386_ = v___x_3380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
                        lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3378_);
                        v___x_3386_ = v_reuseFailAlloc_3387_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_3378_);
                    v_a_3388_ = lean_ctor_get(v___x_3383_, 0);
                    lean_inc(v_a_3388_);
                    lean_dec_ref_known(v___x_3383_, 1);
                    v___x_3389_ = lean_box(0);
                    if v_isShared_3381_ == 0 {
                        lean_ctor_set(v___x_3380_, 1, v_a_3388_);
                        lean_ctor_set(v___x_3380_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3380_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3389_);
                        lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_a_3388_);
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
    mut v_init_3398_: *mut LeanObject,
    mut v_text_3399_: *mut LeanObject,
    mut v_requestedRange_3400_: *mut LeanObject,
    mut v_as_3401_: *mut LeanObject,
    mut v_sz_3402_: *mut LeanObject,
    mut v_i_3403_: *mut LeanObject,
    mut v_b_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3406_: usize = 0;
    let mut v_i_boxed_3407_: usize = 0;
    let mut v_res_3408_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3402_);
    lean_dec(v_sz_3402_);
    v_i_boxed_3407_ = lean_unbox_usize(v_i_3403_);
    lean_dec(v_i_3403_);
    v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_3398_, v_text_3399_, v_requestedRange_3400_, v_as_3401_, v_sz_boxed_3406_, v_i_boxed_3407_, v_b_3404_);
    lean_dec_ref(v_as_3401_);
    lean_dec_ref(v_requestedRange_3400_);
    lean_dec_ref(v_text_3399_);
    lean_dec_ref(v_init_3398_);
    return v_res_3408_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(
    mut v_init_3409_: *mut LeanObject,
    mut v_text_3410_: *mut LeanObject,
    mut v_requestedRange_3411_: *mut LeanObject,
    mut v_n_3412_: *mut LeanObject,
    mut v_b_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3415_: *mut LeanObject = core::ptr::null_mut();
    v_res_3415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3409_, v_text_3410_, v_requestedRange_3411_, v_n_3412_, v_b_3413_);
    lean_dec_ref(v_n_3412_);
    lean_dec_ref(v_requestedRange_3411_);
    lean_dec_ref(v_text_3410_);
    lean_dec_ref(v_init_3409_);
    return v_res_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(
    mut v_text_3416_: *mut LeanObject,
    mut v_requestedRange_3417_: *mut LeanObject,
    mut v_as_3418_: *mut LeanObject,
    mut v_sz_3419_: usize,
    mut v_i_3420_: usize,
    mut v_b_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3423_: u8 = 0;
    let mut v_snd_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v_a_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: usize = 0;
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_ranges_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_unused_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3423_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
                if v___x_3423_ == 0 {
                    return v_b_3421_;
                } else {
                    v_snd_3424_ = lean_ctor_get(v_b_3421_, 1);
                    v_isSharedCheck_3451_ = (!lean_is_exclusive(v_b_3421_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v_unused_3452_ = lean_ctor_get(v_b_3421_, 0);
                        lean_dec(v_unused_3452_);
                        v___x_3426_ = v_b_3421_;
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3424_);
                        lean_dec(v_b_3421_);
                        v___x_3426_ = lean_box(0);
                        v_isShared_3427_ = v_isSharedCheck_3451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3428_ = lean_array_uget_borrowed(v_as_3418_, v_i_3420_);
                v_pos_3429_ = lean_ctor_get(v_a_3428_, 1);
                v_endPos_3430_ = lean_ctor_get(v_a_3428_, 2);
                v_data_3431_ = lean_ctor_get(v_a_3428_, 4);
                v___f_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3433_ = lean_box(0);
                lean_inc(v_data_3431_);
                v___x_3442_ = l_Lean_MessageData_hasTag(v___f_3432_, v_data_3431_);
                if v___x_3442_ == 0 {
                    v_a_3435_ = v_snd_3424_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3429_);
                    v___x_3443_ = l_Lean_FileMap_ofPosition(v_text_3416_, v_pos_3429_);
                    if lean_obj_tag(v_endPos_3430_) == 0 {
                        lean_inc_ref(v_pos_3429_);
                        v___y_3445_ = v_pos_3429_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3450_ = lean_ctor_get(v_endPos_3430_, 0);
                        lean_inc(v_val_3450_);
                        v___y_3445_ = v_val_3450_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3427_ == 0 {
                    lean_ctor_set(v___x_3426_, 1, v_a_3435_);
                    lean_ctor_set(v___x_3426_, 0, v___x_3433_);
                    v___x_3437_ = v___x_3426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3433_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3435_);
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
                v_msgRange_3447_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3447_, 0, v___x_3443_);
                lean_ctor_set(v_msgRange_3447_, 1, v___x_3446_);
                v___x_3448_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3447_,
                    v_requestedRange_3417_,
                    v___x_3442_,
                    v___x_3442_,
                );
                if v___x_3448_ == 0 {
                    lean_dec_ref_known(v_msgRange_3447_, 2);
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
    mut v_text_3453_: *mut LeanObject,
    mut v_requestedRange_3454_: *mut LeanObject,
    mut v_as_3455_: *mut LeanObject,
    mut v_sz_3456_: *mut LeanObject,
    mut v_i_3457_: *mut LeanObject,
    mut v_b_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3460_: usize = 0;
    let mut v_i_boxed_3461_: usize = 0;
    let mut v_res_3462_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3460_ = lean_unbox_usize(v_sz_3456_);
    lean_dec(v_sz_3456_);
    v_i_boxed_3461_ = lean_unbox_usize(v_i_3457_);
    lean_dec(v_i_3457_);
    v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_3453_, v_requestedRange_3454_, v_as_3455_, v_sz_boxed_3460_, v_i_boxed_3461_, v_b_3458_);
    lean_dec_ref(v_as_3455_);
    lean_dec_ref(v_requestedRange_3454_);
    lean_dec_ref(v_text_3453_);
    return v_res_3462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(
    mut v_text_3463_: *mut LeanObject,
    mut v_requestedRange_3464_: *mut LeanObject,
    mut v_as_3465_: *mut LeanObject,
    mut v_sz_3466_: usize,
    mut v_i_3467_: usize,
    mut v_b_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3470_: u8 = 0;
    let mut v_snd_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_a_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v_ranges_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v_unused_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
                if v___x_3470_ == 0 {
                    return v_b_3468_;
                } else {
                    v_snd_3471_ = lean_ctor_get(v_b_3468_, 1);
                    v_isSharedCheck_3498_ = (!lean_is_exclusive(v_b_3468_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v_unused_3499_ = lean_ctor_get(v_b_3468_, 0);
                        lean_dec(v_unused_3499_);
                        v___x_3473_ = v_b_3468_;
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3471_);
                        lean_dec(v_b_3468_);
                        v___x_3473_ = lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3475_ = lean_array_uget_borrowed(v_as_3465_, v_i_3467_);
                v_pos_3476_ = lean_ctor_get(v_a_3475_, 1);
                v_endPos_3477_ = lean_ctor_get(v_a_3475_, 2);
                v_data_3478_ = lean_ctor_get(v_a_3475_, 4);
                v___f_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3480_ = lean_box(0);
                lean_inc(v_data_3478_);
                v___x_3489_ = l_Lean_MessageData_hasTag(v___f_3479_, v_data_3478_);
                if v___x_3489_ == 0 {
                    v_a_3482_ = v_snd_3471_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3476_);
                    v___x_3490_ = l_Lean_FileMap_ofPosition(v_text_3463_, v_pos_3476_);
                    if lean_obj_tag(v_endPos_3477_) == 0 {
                        lean_inc_ref(v_pos_3476_);
                        v___y_3492_ = v_pos_3476_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3497_ = lean_ctor_get(v_endPos_3477_, 0);
                        lean_inc(v_val_3497_);
                        v___y_3492_ = v_val_3497_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3474_ == 0 {
                    lean_ctor_set(v___x_3473_, 1, v_a_3482_);
                    lean_ctor_set(v___x_3473_, 0, v___x_3480_);
                    v___x_3484_ = v___x_3473_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3480_);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_a_3482_);
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
                v_msgRange_3494_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3494_, 0, v___x_3490_);
                lean_ctor_set(v_msgRange_3494_, 1, v___x_3493_);
                v___x_3495_ = l_Lean_Syntax_Range_overlaps(
                    v_msgRange_3494_,
                    v_requestedRange_3464_,
                    v___x_3489_,
                    v___x_3489_,
                );
                if v___x_3495_ == 0 {
                    lean_dec_ref_known(v_msgRange_3494_, 2);
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
    mut v_text_3500_: *mut LeanObject,
    mut v_requestedRange_3501_: *mut LeanObject,
    mut v_as_3502_: *mut LeanObject,
    mut v_sz_3503_: *mut LeanObject,
    mut v_i_3504_: *mut LeanObject,
    mut v_b_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3507_: usize = 0;
    let mut v_i_boxed_3508_: usize = 0;
    let mut v_res_3509_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3507_ = lean_unbox_usize(v_sz_3503_);
    lean_dec(v_sz_3503_);
    v_i_boxed_3508_ = lean_unbox_usize(v_i_3504_);
    lean_dec(v_i_3504_);
    v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3500_, v_requestedRange_3501_, v_as_3502_, v_sz_boxed_3507_, v_i_boxed_3508_, v_b_3505_);
    lean_dec_ref(v_as_3502_);
    lean_dec_ref(v_requestedRange_3501_);
    lean_dec_ref(v_text_3500_);
    return v_res_3509_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(
    mut v_text_3510_: *mut LeanObject,
    mut v_requestedRange_3511_: *mut LeanObject,
    mut v_t_3512_: *mut LeanObject,
    mut v_init_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v_root_3515_ = lean_ctor_get(v_t_3512_, 0);
    v_tail_3516_ = lean_ctor_get(v_t_3512_, 1);
    lean_inc_ref(v_init_3513_);
    v___x_3517_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_3513_, v_text_3510_, v_requestedRange_3511_, v_root_3515_, v_init_3513_);
    lean_dec_ref(v_init_3513_);
    if lean_obj_tag(v___x_3517_) == 0 {
        let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
        v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
        lean_inc(v_a_3518_);
        lean_dec_ref_known(v___x_3517_, 1);
        return v_a_3518_;
    } else {
        let mut v_a_3519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3522_: usize = 0;
        let mut v___x_3523_: usize = 0;
        let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3525_: *mut LeanObject = core::ptr::null_mut();
        v_a_3519_ = lean_ctor_get(v___x_3517_, 0);
        lean_inc(v_a_3519_);
        lean_dec_ref_known(v___x_3517_, 1);
        v___x_3520_ = lean_box(0);
        v___x_3521_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3521_, 0, v___x_3520_);
        lean_ctor_set(v___x_3521_, 1, v_a_3519_);
        v_sz_3522_ = lean_array_size(v_tail_3516_);
        v___x_3523_ = 0usize;
        v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_3510_, v_requestedRange_3511_, v_tail_3516_, v_sz_3522_, v___x_3523_, v___x_3521_);
        v_fst_3525_ = lean_ctor_get(v___x_3524_, 0);
        lean_inc(v_fst_3525_);
        if lean_obj_tag(v_fst_3525_) == 0 {
            let mut v_snd_3526_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3526_ = lean_ctor_get(v___x_3524_, 1);
            lean_inc(v_snd_3526_);
            lean_dec_ref(v___x_3524_);
            return v_snd_3526_;
        } else {
            let mut v_val_3527_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3524_);
            v_val_3527_ = lean_ctor_get(v_fst_3525_, 0);
            lean_inc(v_val_3527_);
            lean_dec_ref_known(v_fst_3525_, 1);
            return v_val_3527_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(
    mut v_text_3528_: *mut LeanObject,
    mut v_requestedRange_3529_: *mut LeanObject,
    mut v_t_3530_: *mut LeanObject,
    mut v_init_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3533_: *mut LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3528_, v_requestedRange_3529_, v_t_3530_, v_init_3531_);
    lean_dec_ref(v_t_3530_);
    lean_dec_ref(v_requestedRange_3529_);
    lean_dec_ref(v_text_3528_);
    return v_res_3533_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(
    mut v_init_3534_: *mut LeanObject,
    mut v_x_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3535_) == 0 {
                    v_k_3536_ = lean_ctor_get(v_x_3535_, 1);
                    lean_inc(v_k_3536_);
                    v_l_3537_ = lean_ctor_get(v_x_3535_, 3);
                    lean_inc(v_l_3537_);
                    v_r_3538_ = lean_ctor_get(v_x_3535_, 4);
                    lean_inc(v_r_3538_);
                    lean_dec_ref_known(v_x_3535_, 5);
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
    mut v_doc_3549_: *mut LeanObject,
    mut v_requestedRange_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEditableDocumentCore_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unreported_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: u8 = 0;
    let mut v___y_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_3552_ = lean_ctor_get(v_doc_3549_, 0);
                lean_inc_ref(v_toEditableDocumentCore_3552_);
                v_start_3553_ = lean_ctor_get(v_requestedRange_3550_, 0);
                lean_inc(v_start_3553_);
                v___x_3554_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_3549_, v_start_3553_);
                v___x_3555_ = lean_task_get_own(v___x_3554_);
                if lean_obj_tag(v___x_3555_) == 1 {
                    v_meta_3556_ = lean_ctor_get(v_toEditableDocumentCore_3552_, 0);
                    lean_inc_ref(v_meta_3556_);
                    lean_dec_ref(v_toEditableDocumentCore_3552_);
                    v_val_3557_ = lean_ctor_get(v___x_3555_, 0);
                    lean_inc(v_val_3557_);
                    lean_dec_ref_known(v___x_3555_, 1);
                    v_text_3558_ = lean_ctor_get(v_meta_3556_, 3);
                    lean_inc_ref(v_text_3558_);
                    lean_dec_ref(v_meta_3556_);
                    v_elabSnap_3559_ = lean_ctor_get(v_val_3557_, 3);
                    lean_inc_ref(v_elabSnap_3559_);
                    lean_dec(v_val_3557_);
                    v_tree_3560_ =
                        l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(
                            v_elabSnap_3559_,
                        );
                    lean_inc_ref(v_requestedRange_3550_);
                    lean_inc_ref(v_tree_3560_);
                    v___x_3561_ = l_Lean_Language_SnapshotTree_collectMessagesInRange(
                        v_tree_3560_,
                        v_requestedRange_3550_,
                    );
                    v_msgLog_3562_ = lean_task_get_own(v___x_3561_);
                    v_unreported_3563_ = lean_ctor_get(v_msgLog_3562_, 1);
                    lean_inc_ref(v_unreported_3563_);
                    lean_dec(v_msgLog_3562_);
                    v___x_3564_ = lean_unsigned_to_nat(0);
                    v_ranges_3565_ =
                        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                    v___x_3566_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_3558_, v_requestedRange_3550_, v_unreported_3563_, v_ranges_3565_);
                    lean_dec_ref(v_unreported_3563_);
                    lean_dec_ref(v_text_3558_);
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
                    lean_dec(v___x_3555_);
                    lean_dec_ref(v_toEditableDocumentCore_3552_);
                    lean_dec_ref(v_requestedRange_3550_);
                    v___x_3587_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2;
                    return v___x_3587_;
                }
            }
            1 => {
                v___x_3571_ = lean_mk_empty_array_with_capacity(v___y_3570_);
                lean_dec(v___y_3570_);
                v___x_3572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3571_, v___y_3568_);
                v___x_3573_ = l_Array_append___redArg(v___x_3566_, v___x_3572_);
                lean_dec_ref(v___x_3572_);
                v___x_3574_ = lean_box((v___y_3569_) as usize);
                v___x_3575_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                return v___x_3575_;
            }
            2 => {
                v___x_3579_ = lean_box(1);
                v___x_3580_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(
                    v_tree_3560_,
                    v_requestedRange_3550_,
                    v___x_3579_,
                    v___f_3576_,
                );
                v___x_3581_ = lean_task_get_own(v___x_3580_);
                if lean_obj_tag(v___x_3581_) == 0 {
                    v_size_3582_ = lean_ctor_get(v___x_3581_, 0);
                    lean_inc(v_size_3582_);
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
    mut v_doc_3588_: *mut LeanObject,
    mut v_requestedRange_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3591_: *mut LeanObject = core::ptr::null_mut();
    v_res_3591_ =
        l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(v_doc_3588_, v_requestedRange_3589_);
    return v_res_3591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(
    mut v_00_u03b2_3592_: *mut LeanObject,
    mut v_k_3593_: *mut LeanObject,
    mut v_t_3594_: *mut LeanObject,
) -> u8 {
    let mut v___x_3595_: u8 = 0;
    v___x_3595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_3593_, v_t_3594_);
    return v___x_3595_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(
    mut v_00_u03b2_3596_: *mut LeanObject,
    mut v_k_3597_: *mut LeanObject,
    mut v_t_3598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3599_: u8 = 0;
    let mut v_r_3600_: *mut LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_00_u03b2_3596_, v_k_3597_, v_t_3598_);
    lean_dec(v_t_3598_);
    lean_dec_ref(v_k_3597_);
    v_r_3600_ = lean_box((v_res_3599_) as usize);
    return v_r_3600_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(
    mut v_00_u03b2_3601_: *mut LeanObject,
    mut v_k_3602_: *mut LeanObject,
    mut v_v_3603_: *mut LeanObject,
    mut v_t_3604_: *mut LeanObject,
    mut v_hl_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_3602_, v_v_3603_, v_t_3604_);
    return v___x_3606_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(
    mut v_init_3607_: *mut LeanObject,
    mut v_t_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    v___x_3609_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_3607_, v_t_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(
    mut v_s_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    v___x_3613_ =
        l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0;
    v___x_3614_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3614_, 0, v_s_3612_);
    lean_ctor_set(v___x_3614_, 1, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(
    mut v___f_3616_: *mut LeanObject,
    mut v_s_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSnapshot_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v_firstCmdSnap_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_3618_ = lean_ctor_get(v_s_3617_, 0);
                lean_inc_ref(v_toSnapshot_3618_);
                v_metaSnap_3619_ = lean_ctor_get(v_s_3617_, 1);
                lean_inc_ref(v_metaSnap_3619_);
                v_result_x3f_3620_ = lean_ctor_get(v_s_3617_, 2);
                lean_inc(v_result_x3f_3620_);
                lean_dec_ref(v_s_3617_);
                if lean_obj_tag(v_result_x3f_3620_) == 0 {
                    v___x_3632_ = lean_box(0);
                    v___y_3622_ = v___x_3632_;
                    state = 1;
                    continue;
                } else {
                    v_val_3633_ = lean_ctor_get(v_result_x3f_3620_, 0);
                    v_isSharedCheck_3646_ = (!lean_is_exclusive(v_result_x3f_3620_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3635_ = v_result_x3f_3620_;
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3633_);
                        lean_dec(v_result_x3f_3620_);
                        v___x_3635_ = lean_box(0);
                        v_isShared_3636_ = v_isSharedCheck_3646_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_3623_ = lean_ctor_get(v_metaSnap_3619_, 0);
                lean_inc(v_stx_x3f_3623_);
                v_reportingRange_3624_ = lean_ctor_get(v_metaSnap_3619_, 1);
                lean_inc(v_reportingRange_3624_);
                v___x_3625_ = 1;
                v___x_3626_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_3619_,
                    v___f_3616_,
                    v_stx_x3f_3623_,
                    v_reportingRange_3624_,
                    v___x_3625_,
                );
                v___x_3627_ = lean_unsigned_to_nat(1);
                v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
                v___x_3629_ = lean_array_push(v___x_3628_, v___x_3626_);
                v___x_3630_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_3622_, v___x_3629_);
                v___x_3631_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3631_, 0, v_toSnapshot_3618_);
                lean_ctor_set(v___x_3631_, 1, v___x_3630_);
                return v___x_3631_;
            }
            2 => {
                v_firstCmdSnap_3637_ = lean_ctor_get(v_val_3633_, 1);
                lean_inc_ref(v_firstCmdSnap_3637_);
                lean_dec(v_val_3633_);
                v_stx_x3f_3638_ = lean_ctor_get(v_firstCmdSnap_3637_, 0);
                lean_inc(v_stx_x3f_3638_);
                v_reportingRange_3639_ = lean_ctor_get(v_firstCmdSnap_3637_, 1);
                lean_inc(v_reportingRange_3639_);
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
                    lean_ctor_set(v___x_3635_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
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
    mut v_as_3647_: *mut LeanObject,
    mut v_i_3648_: usize,
    mut v_stop_3649_: usize,
    mut v_b_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3651_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = lean_usize_dec_eq(v_i_3648_, v_stop_3649_);
                if v___x_3651_ == 0 {
                    v___x_3652_ = lean_array_uget_borrowed(v_as_3647_, v_i_3648_);
                    lean_inc(v___x_3652_);
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
    mut v_as_3657_: *mut LeanObject,
    mut v_i_3658_: *mut LeanObject,
    mut v_stop_3659_: *mut LeanObject,
    mut v_b_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3661_: usize = 0;
    let mut v_stop_boxed_3662_: usize = 0;
    let mut v_res_3663_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3661_ = lean_unbox_usize(v_i_3658_);
    lean_dec(v_i_3658_);
    v_stop_boxed_3662_ = lean_unbox_usize(v_stop_3659_);
    lean_dec(v_stop_3659_);
    v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v_as_3657_, v_i_boxed_3661_, v_stop_boxed_3662_, v_b_3660_);
    lean_dec_ref(v_as_3657_);
    return v_res_3663_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(
    mut v_as_x27_3664_: *mut LeanObject,
    mut v_b_3665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3664_) == 0 {
                    return v_b_3665_;
                } else {
                    v_head_3667_ = lean_ctor_get(v_as_x27_3664_, 0);
                    v_tail_3668_ = lean_ctor_get(v_as_x27_3664_, 1);
                    v___f_3669_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3670_ = lean_box(1);
                    lean_inc(v_head_3667_);
                    v___x_3671_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3667_);
                    v___x_3672_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3669_,
                        v___x_3670_,
                        v___x_3671_,
                    );
                    if lean_obj_tag(v___x_3672_) == 0 {
                        v_size_3679_ = lean_ctor_get(v___x_3672_, 0);
                        lean_inc(v_size_3679_);
                        v___y_3674_ = v_size_3679_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3680_ = lean_unsigned_to_nat(0);
                        v___y_3674_ = v___x_3680_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3675_ = lean_mk_empty_array_with_capacity(v___y_3674_);
                lean_dec(v___y_3674_);
                v___x_3676_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3675_, v___x_3672_);
                v___x_3677_ = l_Array_append___redArg(v_b_3665_, v___x_3676_);
                lean_dec_ref(v___x_3676_);
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
    mut v_as_x27_3681_: *mut LeanObject,
    mut v_b_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3684_: *mut LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_3681_, v_b_3682_);
    lean_dec(v_as_x27_3681_);
    return v_res_3684_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(
    mut v_as_3685_: *mut LeanObject,
    mut v_as_x27_3686_: *mut LeanObject,
    mut v_b_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3686_) == 0 {
                    return v_b_3687_;
                } else {
                    v_head_3689_ = lean_ctor_get(v_as_x27_3686_, 0);
                    v_tail_3690_ = lean_ctor_get(v_as_x27_3686_, 1);
                    v___f_3691_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
                    v___x_3692_ = lean_box(1);
                    lean_inc(v_head_3689_);
                    v___x_3693_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3689_);
                    v___x_3694_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_3691_,
                        v___x_3692_,
                        v___x_3693_,
                    );
                    if lean_obj_tag(v___x_3694_) == 0 {
                        v_size_3701_ = lean_ctor_get(v___x_3694_, 0);
                        lean_inc(v_size_3701_);
                        v___y_3696_ = v_size_3701_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3702_ = lean_unsigned_to_nat(0);
                        v___y_3696_ = v___x_3702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3697_ = lean_mk_empty_array_with_capacity(v___y_3696_);
                lean_dec(v___y_3696_);
                v___x_3698_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_3697_, v___x_3694_);
                v___x_3699_ = l_Array_append___redArg(v_b_3687_, v___x_3698_);
                lean_dec_ref(v___x_3698_);
                v___x_3700_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_tail_3690_, v___x_3699_);
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(
    mut v_as_3703_: *mut LeanObject,
    mut v_as_x27_3704_: *mut LeanObject,
    mut v_b_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3707_: *mut LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_3703_, v_as_x27_3704_, v_b_3705_);
    lean_dec(v_as_x27_3704_);
    lean_dec(v_as_3703_);
    return v_res_3707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(
    mut v_text_3708_: *mut LeanObject,
    mut v_as_3709_: *mut LeanObject,
    mut v_sz_3710_: usize,
    mut v_i_3711_: usize,
    mut v_b_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3714_: u8 = 0;
    let mut v_snd_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v_a_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: usize = 0;
    let mut v_reuseFailAlloc_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_unused_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3714_ = lean_usize_dec_lt(v_i_3711_, v_sz_3710_);
                if v___x_3714_ == 0 {
                    return v_b_3712_;
                } else {
                    v_snd_3715_ = lean_ctor_get(v_b_3712_, 1);
                    v_isSharedCheck_3741_ = (!lean_is_exclusive(v_b_3712_)) as u8;
                    if v_isSharedCheck_3741_ == 0 {
                        v_unused_3742_ = lean_ctor_get(v_b_3712_, 0);
                        lean_dec(v_unused_3742_);
                        v___x_3717_ = v_b_3712_;
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3715_);
                        lean_dec(v_b_3712_);
                        v___x_3717_ = lean_box(0);
                        v_isShared_3718_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3719_ = lean_array_uget_borrowed(v_as_3709_, v_i_3711_);
                v_pos_3720_ = lean_ctor_get(v_a_3719_, 1);
                v_endPos_3721_ = lean_ctor_get(v_a_3719_, 2);
                v_data_3722_ = lean_ctor_get(v_a_3719_, 4);
                v___f_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3724_ = lean_box(0);
                lean_inc(v_data_3722_);
                v___x_3733_ = l_Lean_MessageData_hasTag(v___f_3723_, v_data_3722_);
                if v___x_3733_ == 0 {
                    v_a_3726_ = v_snd_3715_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3720_);
                    v___x_3734_ = l_Lean_FileMap_ofPosition(v_text_3708_, v_pos_3720_);
                    if lean_obj_tag(v_endPos_3721_) == 0 {
                        lean_inc_ref(v_pos_3720_);
                        v___y_3736_ = v_pos_3720_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3740_ = lean_ctor_get(v_endPos_3721_, 0);
                        lean_inc(v_val_3740_);
                        v___y_3736_ = v_val_3740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3718_ == 0 {
                    lean_ctor_set(v___x_3717_, 1, v_a_3726_);
                    lean_ctor_set(v___x_3717_, 0, v___x_3724_);
                    v___x_3728_ = v___x_3717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3724_);
                    lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_a_3726_);
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
                v_msgRange_3738_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3738_, 0, v___x_3734_);
                lean_ctor_set(v_msgRange_3738_, 1, v___x_3737_);
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
    mut v_text_3743_: *mut LeanObject,
    mut v_as_3744_: *mut LeanObject,
    mut v_sz_3745_: *mut LeanObject,
    mut v_i_3746_: *mut LeanObject,
    mut v_b_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3749_: usize = 0;
    let mut v_i_boxed_3750_: usize = 0;
    let mut v_res_3751_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3745_);
    lean_dec(v_sz_3745_);
    v_i_boxed_3750_ = lean_unbox_usize(v_i_3746_);
    lean_dec(v_i_3746_);
    v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_3743_, v_as_3744_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3747_);
    lean_dec_ref(v_as_3744_);
    lean_dec_ref(v_text_3743_);
    return v_res_3751_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(
    mut v_text_3752_: *mut LeanObject,
    mut v_as_3753_: *mut LeanObject,
    mut v_sz_3754_: usize,
    mut v_i_3755_: usize,
    mut v_b_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3758_: u8 = 0;
    let mut v_snd_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: usize = 0;
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
                if v___x_3758_ == 0 {
                    return v_b_3756_;
                } else {
                    v_snd_3759_ = lean_ctor_get(v_b_3756_, 1);
                    v_isSharedCheck_3785_ = (!lean_is_exclusive(v_b_3756_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v_unused_3786_ = lean_ctor_get(v_b_3756_, 0);
                        lean_dec(v_unused_3786_);
                        v___x_3761_ = v_b_3756_;
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3759_);
                        lean_dec(v_b_3756_);
                        v___x_3761_ = lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3763_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
                v_pos_3764_ = lean_ctor_get(v_a_3763_, 1);
                v_endPos_3765_ = lean_ctor_get(v_a_3763_, 2);
                v_data_3766_ = lean_ctor_get(v_a_3763_, 4);
                v___f_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3768_ = lean_box(0);
                lean_inc(v_data_3766_);
                v___x_3777_ = l_Lean_MessageData_hasTag(v___f_3767_, v_data_3766_);
                if v___x_3777_ == 0 {
                    v_a_3770_ = v_snd_3759_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3764_);
                    v___x_3778_ = l_Lean_FileMap_ofPosition(v_text_3752_, v_pos_3764_);
                    if lean_obj_tag(v_endPos_3765_) == 0 {
                        lean_inc_ref(v_pos_3764_);
                        v___y_3780_ = v_pos_3764_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3784_ = lean_ctor_get(v_endPos_3765_, 0);
                        lean_inc(v_val_3784_);
                        v___y_3780_ = v_val_3784_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3762_ == 0 {
                    lean_ctor_set(v___x_3761_, 1, v_a_3770_);
                    lean_ctor_set(v___x_3761_, 0, v___x_3768_);
                    v___x_3772_ = v___x_3761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_a_3770_);
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
                v_msgRange_3782_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3782_, 0, v___x_3778_);
                lean_ctor_set(v_msgRange_3782_, 1, v___x_3781_);
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
    mut v_text_3787_: *mut LeanObject,
    mut v_as_3788_: *mut LeanObject,
    mut v_sz_3789_: *mut LeanObject,
    mut v_i_3790_: *mut LeanObject,
    mut v_b_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3793_: usize = 0;
    let mut v_i_boxed_3794_: usize = 0;
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3793_ = lean_unbox_usize(v_sz_3789_);
    lean_dec(v_sz_3789_);
    v_i_boxed_3794_ = lean_unbox_usize(v_i_3790_);
    lean_dec(v_i_3790_);
    v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3787_, v_as_3788_, v_sz_boxed_3793_, v_i_boxed_3794_, v_b_3791_);
    lean_dec_ref(v_as_3788_);
    lean_dec_ref(v_text_3787_);
    return v_res_3795_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(
    mut v_text_3796_: *mut LeanObject,
    mut v_as_3797_: *mut LeanObject,
    mut v_sz_3798_: usize,
    mut v_i_3799_: usize,
    mut v_b_3800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3802_: u8 = 0;
    let mut v_snd_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_a_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: usize = 0;
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_unused_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
                if v___x_3802_ == 0 {
                    return v_b_3800_;
                } else {
                    v_snd_3803_ = lean_ctor_get(v_b_3800_, 1);
                    v_isSharedCheck_3829_ = (!lean_is_exclusive(v_b_3800_)) as u8;
                    if v_isSharedCheck_3829_ == 0 {
                        v_unused_3830_ = lean_ctor_get(v_b_3800_, 0);
                        lean_dec(v_unused_3830_);
                        v___x_3805_ = v_b_3800_;
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3803_);
                        lean_dec(v_b_3800_);
                        v___x_3805_ = lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3807_ = lean_array_uget_borrowed(v_as_3797_, v_i_3799_);
                v_pos_3808_ = lean_ctor_get(v_a_3807_, 1);
                v_endPos_3809_ = lean_ctor_get(v_a_3807_, 2);
                v_data_3810_ = lean_ctor_get(v_a_3807_, 4);
                v___f_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3812_ = lean_box(0);
                lean_inc(v_data_3810_);
                v___x_3821_ = l_Lean_MessageData_hasTag(v___f_3811_, v_data_3810_);
                if v___x_3821_ == 0 {
                    v_a_3814_ = v_snd_3803_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3808_);
                    v___x_3822_ = l_Lean_FileMap_ofPosition(v_text_3796_, v_pos_3808_);
                    if lean_obj_tag(v_endPos_3809_) == 0 {
                        lean_inc_ref(v_pos_3808_);
                        v___y_3824_ = v_pos_3808_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3828_ = lean_ctor_get(v_endPos_3809_, 0);
                        lean_inc(v_val_3828_);
                        v___y_3824_ = v_val_3828_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3806_ == 0 {
                    lean_ctor_set(v___x_3805_, 1, v_a_3814_);
                    lean_ctor_set(v___x_3805_, 0, v___x_3812_);
                    v___x_3816_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3812_);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3814_);
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
                v_msgRange_3826_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3826_, 0, v___x_3822_);
                lean_ctor_set(v_msgRange_3826_, 1, v___x_3825_);
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
    mut v_text_3831_: *mut LeanObject,
    mut v_as_3832_: *mut LeanObject,
    mut v_sz_3833_: *mut LeanObject,
    mut v_i_3834_: *mut LeanObject,
    mut v_b_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3837_: usize = 0;
    let mut v_i_boxed_3838_: usize = 0;
    let mut v_res_3839_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3837_ = lean_unbox_usize(v_sz_3833_);
    lean_dec(v_sz_3833_);
    v_i_boxed_3838_ = lean_unbox_usize(v_i_3834_);
    lean_dec(v_i_3834_);
    v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_3831_, v_as_3832_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3835_);
    lean_dec_ref(v_as_3832_);
    lean_dec_ref(v_text_3831_);
    return v_res_3839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(
    mut v_text_3840_: *mut LeanObject,
    mut v_as_3841_: *mut LeanObject,
    mut v_sz_3842_: usize,
    mut v_i_3843_: usize,
    mut v_b_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: u8 = 0;
    let mut v_snd_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v_a_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: usize = 0;
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgRange_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_unused_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3846_ = lean_usize_dec_lt(v_i_3843_, v_sz_3842_);
                if v___x_3846_ == 0 {
                    return v_b_3844_;
                } else {
                    v_snd_3847_ = lean_ctor_get(v_b_3844_, 1);
                    v_isSharedCheck_3873_ = (!lean_is_exclusive(v_b_3844_)) as u8;
                    if v_isSharedCheck_3873_ == 0 {
                        v_unused_3874_ = lean_ctor_get(v_b_3844_, 0);
                        lean_dec(v_unused_3874_);
                        v___x_3849_ = v_b_3844_;
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3847_);
                        lean_dec(v_b_3844_);
                        v___x_3849_ = lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3873_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3851_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
                v_pos_3852_ = lean_ctor_get(v_a_3851_, 1);
                v_endPos_3853_ = lean_ctor_get(v_a_3851_, 2);
                v_data_3854_ = lean_ctor_get(v_a_3851_, 4);
                v___f_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0;
                v___x_3856_ = lean_box(0);
                lean_inc(v_data_3854_);
                v___x_3865_ = l_Lean_MessageData_hasTag(v___f_3855_, v_data_3854_);
                if v___x_3865_ == 0 {
                    v_a_3858_ = v_snd_3847_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_pos_3852_);
                    v___x_3866_ = l_Lean_FileMap_ofPosition(v_text_3840_, v_pos_3852_);
                    if lean_obj_tag(v_endPos_3853_) == 0 {
                        lean_inc_ref(v_pos_3852_);
                        v___y_3868_ = v_pos_3852_;
                        state = 4;
                        continue;
                    } else {
                        v_val_3872_ = lean_ctor_get(v_endPos_3853_, 0);
                        lean_inc(v_val_3872_);
                        v___y_3868_ = v_val_3872_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3850_ == 0 {
                    lean_ctor_set(v___x_3849_, 1, v_a_3858_);
                    lean_ctor_set(v___x_3849_, 0, v___x_3856_);
                    v___x_3860_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3856_);
                    lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_a_3858_);
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
                v_msgRange_3870_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_msgRange_3870_, 0, v___x_3866_);
                lean_ctor_set(v_msgRange_3870_, 1, v___x_3869_);
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
    mut v_text_3875_: *mut LeanObject,
    mut v_as_3876_: *mut LeanObject,
    mut v_sz_3877_: *mut LeanObject,
    mut v_i_3878_: *mut LeanObject,
    mut v_b_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3881_: usize = 0;
    let mut v_i_boxed_3882_: usize = 0;
    let mut v_res_3883_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3881_ = lean_unbox_usize(v_sz_3877_);
    lean_dec(v_sz_3877_);
    v_i_boxed_3882_ = lean_unbox_usize(v_i_3878_);
    lean_dec(v_i_3878_);
    v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3875_, v_as_3876_, v_sz_boxed_3881_, v_i_boxed_3882_, v_b_3879_);
    lean_dec_ref(v_as_3876_);
    lean_dec_ref(v_text_3875_);
    return v_res_3883_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(
    mut v_init_3884_: *mut LeanObject,
    mut v_text_3885_: *mut LeanObject,
    mut v_n_3886_: *mut LeanObject,
    mut v_b_3887_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_n_3886_) == 0 {
        let mut v_cs_3889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3892_: usize = 0;
        let mut v___x_3893_: usize = 0;
        let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3895_: *mut LeanObject = core::ptr::null_mut();
        v_cs_3889_ = lean_ctor_get(v_n_3886_, 0);
        v___x_3890_ = lean_box(0);
        v___x_3891_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3891_, 0, v___x_3890_);
        lean_ctor_set(v___x_3891_, 1, v_b_3887_);
        v_sz_3892_ = lean_array_size(v_cs_3889_);
        v___x_3893_ = 0usize;
        v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3884_, v_text_3885_, v_cs_3889_, v_sz_3892_, v___x_3893_, v___x_3891_);
        v_fst_3895_ = lean_ctor_get(v___x_3894_, 0);
        lean_inc(v_fst_3895_);
        if lean_obj_tag(v_fst_3895_) == 0 {
            let mut v_snd_3896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3896_ = lean_ctor_get(v___x_3894_, 1);
            lean_inc(v_snd_3896_);
            lean_dec_ref(v___x_3894_);
            v___x_3897_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3897_, 0, v_snd_3896_);
            return v___x_3897_;
        } else {
            let mut v_val_3898_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3894_);
            v_val_3898_ = lean_ctor_get(v_fst_3895_, 0);
            lean_inc(v_val_3898_);
            lean_dec_ref_known(v_fst_3895_, 1);
            return v_val_3898_;
        }
    } else {
        let mut v_vs_3899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3902_: usize = 0;
        let mut v___x_3903_: usize = 0;
        let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3905_: *mut LeanObject = core::ptr::null_mut();
        v_vs_3899_ = lean_ctor_get(v_n_3886_, 0);
        v___x_3900_ = lean_box(0);
        v___x_3901_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3901_, 0, v___x_3900_);
        lean_ctor_set(v___x_3901_, 1, v_b_3887_);
        v_sz_3902_ = lean_array_size(v_vs_3899_);
        v___x_3903_ = 0usize;
        v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_3885_, v_vs_3899_, v_sz_3902_, v___x_3903_, v___x_3901_);
        v_fst_3905_ = lean_ctor_get(v___x_3904_, 0);
        lean_inc(v_fst_3905_);
        if lean_obj_tag(v_fst_3905_) == 0 {
            let mut v_snd_3906_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3906_ = lean_ctor_get(v___x_3904_, 1);
            lean_inc(v_snd_3906_);
            lean_dec_ref(v___x_3904_);
            v___x_3907_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3907_, 0, v_snd_3906_);
            return v___x_3907_;
        } else {
            let mut v_val_3908_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3904_);
            v_val_3908_ = lean_ctor_get(v_fst_3905_, 0);
            lean_inc(v_val_3908_);
            lean_dec_ref_known(v_fst_3905_, 1);
            return v_val_3908_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(
    mut v_init_3909_: *mut LeanObject,
    mut v_text_3910_: *mut LeanObject,
    mut v_as_3911_: *mut LeanObject,
    mut v_sz_3912_: usize,
    mut v_i_3913_: usize,
    mut v_b_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: u8 = 0;
    let mut v_snd_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: usize = 0;
    let mut v___x_3932_: usize = 0;
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = lean_usize_dec_lt(v_i_3913_, v_sz_3912_);
                if v___x_3916_ == 0 {
                    return v_b_3914_;
                } else {
                    v_snd_3917_ = lean_ctor_get(v_b_3914_, 1);
                    v_isSharedCheck_3935_ = (!lean_is_exclusive(v_b_3914_)) as u8;
                    if v_isSharedCheck_3935_ == 0 {
                        v_unused_3936_ = lean_ctor_get(v_b_3914_, 0);
                        lean_dec(v_unused_3936_);
                        v___x_3919_ = v_b_3914_;
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3917_);
                        lean_dec(v_b_3914_);
                        v___x_3919_ = lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3921_ = lean_array_uget_borrowed(v_as_3911_, v_i_3913_);
                lean_inc(v_snd_3917_);
                v___x_3922_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3909_, v_text_3910_, v_a_3921_, v_snd_3917_);
                if lean_obj_tag(v___x_3922_) == 0 {
                    v___x_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                    if v_isShared_3920_ == 0 {
                        lean_ctor_set(v___x_3919_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3917_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_3917_);
                    v_a_3927_ = lean_ctor_get(v___x_3922_, 0);
                    lean_inc(v_a_3927_);
                    lean_dec_ref_known(v___x_3922_, 1);
                    v___x_3928_ = lean_box(0);
                    if v_isShared_3920_ == 0 {
                        lean_ctor_set(v___x_3919_, 1, v_a_3927_);
                        lean_ctor_set(v___x_3919_, 0, v___x_3928_);
                        v___x_3930_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
                        lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_a_3927_);
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
    mut v_init_3937_: *mut LeanObject,
    mut v_text_3938_: *mut LeanObject,
    mut v_as_3939_: *mut LeanObject,
    mut v_sz_3940_: *mut LeanObject,
    mut v_i_3941_: *mut LeanObject,
    mut v_b_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3944_: usize = 0;
    let mut v_i_boxed_3945_: usize = 0;
    let mut v_res_3946_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3940_);
    lean_dec(v_sz_3940_);
    v_i_boxed_3945_ = lean_unbox_usize(v_i_3941_);
    lean_dec(v_i_3941_);
    v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_3937_, v_text_3938_, v_as_3939_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3942_);
    lean_dec_ref(v_as_3939_);
    lean_dec_ref(v_text_3938_);
    lean_dec_ref(v_init_3937_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(
    mut v_init_3947_: *mut LeanObject,
    mut v_text_3948_: *mut LeanObject,
    mut v_n_3949_: *mut LeanObject,
    mut v_b_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3952_: *mut LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3947_, v_text_3948_, v_n_3949_, v_b_3950_);
    lean_dec_ref(v_n_3949_);
    lean_dec_ref(v_text_3948_);
    lean_dec_ref(v_init_3947_);
    return v_res_3952_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(
    mut v_text_3953_: *mut LeanObject,
    mut v_t_3954_: *mut LeanObject,
    mut v_init_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    v_root_3957_ = lean_ctor_get(v_t_3954_, 0);
    v_tail_3958_ = lean_ctor_get(v_t_3954_, 1);
    lean_inc_ref(v_init_3955_);
    v___x_3959_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_3955_, v_text_3953_, v_root_3957_, v_init_3955_);
    lean_dec_ref(v_init_3955_);
    if lean_obj_tag(v___x_3959_) == 0 {
        let mut v_a_3960_: *mut LeanObject = core::ptr::null_mut();
        v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
        lean_inc(v_a_3960_);
        lean_dec_ref_known(v___x_3959_, 1);
        return v_a_3960_;
    } else {
        let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3964_: usize = 0;
        let mut v___x_3965_: usize = 0;
        let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3967_: *mut LeanObject = core::ptr::null_mut();
        v_a_3961_ = lean_ctor_get(v___x_3959_, 0);
        lean_inc(v_a_3961_);
        lean_dec_ref_known(v___x_3959_, 1);
        v___x_3962_ = lean_box(0);
        v___x_3963_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3963_, 0, v___x_3962_);
        lean_ctor_set(v___x_3963_, 1, v_a_3961_);
        v_sz_3964_ = lean_array_size(v_tail_3958_);
        v___x_3965_ = 0usize;
        v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_3953_, v_tail_3958_, v_sz_3964_, v___x_3965_, v___x_3963_);
        v_fst_3967_ = lean_ctor_get(v___x_3966_, 0);
        lean_inc(v_fst_3967_);
        if lean_obj_tag(v_fst_3967_) == 0 {
            let mut v_snd_3968_: *mut LeanObject = core::ptr::null_mut();
            v_snd_3968_ = lean_ctor_get(v___x_3966_, 1);
            lean_inc(v_snd_3968_);
            lean_dec_ref(v___x_3966_);
            return v_snd_3968_;
        } else {
            let mut v_val_3969_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_3966_);
            v_val_3969_ = lean_ctor_get(v_fst_3967_, 0);
            lean_inc(v_val_3969_);
            lean_dec_ref_known(v_fst_3967_, 1);
            return v_val_3969_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(
    mut v_text_3970_: *mut LeanObject,
    mut v_t_3971_: *mut LeanObject,
    mut v_init_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_3970_, v_t_3971_, v_init_3972_);
    lean_dec_ref(v_t_3971_);
    lean_dec_ref(v_text_3970_);
    return v_res_3974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(
    mut v_sz_3975_: usize,
    mut v_i_3976_: usize,
    mut v_bs_3977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3978_: u8 = 0;
    let mut v_v_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgLog_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3978_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
                if v___x_3978_ == 0 {
                    return v_bs_3977_;
                } else {
                    v_v_3979_ = lean_array_uget_borrowed(v_bs_3977_, v_i_3976_);
                    v_diagnostics_3980_ = lean_ctor_get(v_v_3979_, 1);
                    v_msgLog_3981_ = lean_ctor_get(v_diagnostics_3980_, 0);
                    lean_inc_ref(v_msgLog_3981_);
                    v___x_3982_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3988_: *mut LeanObject,
    mut v_i_3989_: *mut LeanObject,
    mut v_bs_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3991_: usize = 0;
    let mut v_i_boxed_3992_: usize = 0;
    let mut v_res_3993_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3991_ = lean_unbox_usize(v_sz_3988_);
    lean_dec(v_sz_3988_);
    v_i_boxed_3992_ = lean_unbox_usize(v_i_3989_);
    lean_dec(v_i_3989_);
    v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_boxed_3991_, v_i_boxed_3992_, v_bs_3990_);
    return v_res_3993_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1()
-> *mut LeanObject {
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    v___x_3995_ = lean_unsigned_to_nat(32);
    v___x_3996_ = lean_mk_empty_array_with_capacity(v___x_3995_);
    v___x_3997_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3997_, 0, v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2()
-> *mut LeanObject {
    let mut v___x_3998_: usize = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    v___x_3998_ = 5usize;
    v___x_3999_ = lean_unsigned_to_nat(0);
    v___x_4000_ = lean_unsigned_to_nat(32);
    v___x_4001_ = lean_mk_empty_array_with_capacity(v___x_4000_);
    v___x_4002_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1,
    );
    v___x_4003_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4003_, 0, v___x_4002_);
    lean_ctor_set(v___x_4003_, 1, v___x_4001_);
    lean_ctor_set(v___x_4003_, 2, v___x_3999_);
    lean_ctor_set(v___x_4003_, 3, v___x_3999_);
    lean_ctor_set_usize(v___x_4003_, 4, v___x_3998_);
    return v___x_4003_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3()
-> *mut LeanObject {
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    v___x_4004_ = l_Lean_NameSet_empty;
    v___x_4005_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once
        ),
        _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2,
    );
    v___x_4006_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4006_, 0, v___x_4005_);
    lean_ctor_set(v___x_4006_, 1, v___x_4005_);
    lean_ctor_set(v___x_4006_, 2, v___x_4004_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(
    mut v_doc_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEditableDocumentCore_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_meta_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSnap_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unreported_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ranges_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unreported_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snaps_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4050_: usize = 0;
    let mut v___x_4051_: usize = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: usize = 0;
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v_processedSnap_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_unused_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4011_ = lean_ctor_get(v_doc_4009_, 0);
                v_isSharedCheck_4076_ = (!lean_is_exclusive(v_doc_4009_)) as u8;
                if v_isSharedCheck_4076_ == 0 {
                    v_unused_4077_ = lean_ctor_get(v_doc_4009_, 1);
                    lean_dec(v_unused_4077_);
                    v___x_4013_ = v_doc_4009_;
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toEditableDocumentCore_4011_);
                    lean_dec(v_doc_4009_);
                    v___x_4013_ = lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4015_ = lean_ctor_get(v_toEditableDocumentCore_4011_, 0);
                lean_inc_ref(v_meta_4015_);
                v_initSnap_4016_ = lean_ctor_get(v_toEditableDocumentCore_4011_, 1);
                lean_inc_ref(v_initSnap_4016_);
                v_cmdSnaps_4017_ = lean_ctor_get(v_toEditableDocumentCore_4011_, 2);
                lean_inc(v_cmdSnaps_4017_);
                lean_dec_ref(v_toEditableDocumentCore_4011_);
                v_text_4018_ = lean_ctor_get(v_meta_4015_, 3);
                lean_inc_ref(v_text_4018_);
                lean_dec_ref(v_meta_4015_);
                v_toSnapshot_4030_ = lean_ctor_get(v_initSnap_4016_, 0);
                lean_inc_ref(v_toSnapshot_4030_);
                v_metaSnap_4031_ = lean_ctor_get(v_initSnap_4016_, 1);
                lean_inc_ref(v_metaSnap_4031_);
                v_result_x3f_4032_ = lean_ctor_get(v_initSnap_4016_, 4);
                lean_inc(v_result_x3f_4032_);
                lean_dec_ref(v_initSnap_4016_);
                v___f_4033_ =
                    l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0;
                if lean_obj_tag(v_result_x3f_4032_) == 0 {
                    v___x_4061_ = lean_box(0);
                    v___y_4035_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_val_4062_ = lean_ctor_get(v_result_x3f_4032_, 0);
                    v_isSharedCheck_4075_ = (!lean_is_exclusive(v_result_x3f_4032_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4064_ = v_result_x3f_4032_;
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_4062_);
                        lean_dec(v_result_x3f_4032_);
                        v___x_4064_ = lean_box(0);
                        v_isShared_4065_ = v_isSharedCheck_4075_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_ranges_4021_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
                v___x_4022_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_4018_, v_unreported_4020_, v_ranges_4021_);
                lean_dec_ref(v_unreported_4020_);
                lean_dec_ref(v_text_4018_);
                v___x_4023_ = l_IO_AsyncList_waitAll___redArg(v_cmdSnaps_4017_);
                v___x_4024_ = lean_task_get_own(v___x_4023_);
                v_fst_4025_ = lean_ctor_get(v___x_4024_, 0);
                lean_inc(v_fst_4025_);
                lean_dec(v___x_4024_);
                v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_fst_4025_, v_fst_4025_, v___x_4022_);
                lean_dec(v_fst_4025_);
                return v___x_4026_;
            }
            3 => {
                v_unreported_4029_ = lean_ctor_get(v___y_4028_, 1);
                lean_inc_ref(v_unreported_4029_);
                lean_dec_ref(v___y_4028_);
                v_unreported_4020_ = v_unreported_4029_;
                state = 2;
                continue;
            }
            4 => {
                v_stx_x3f_4036_ = lean_ctor_get(v_metaSnap_4031_, 0);
                lean_inc(v_stx_x3f_4036_);
                v_reportingRange_4037_ = lean_ctor_get(v_metaSnap_4031_, 1);
                lean_inc(v_reportingRange_4037_);
                v___x_4038_ = 1;
                v___x_4039_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_4031_,
                    v___f_4033_,
                    v_stx_x3f_4036_,
                    v_reportingRange_4037_,
                    v___x_4038_,
                );
                v___x_4040_ = lean_unsigned_to_nat(1);
                v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_4040_);
                v___x_4042_ = lean_array_push(v___x_4041_, v___x_4039_);
                v___x_4043_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_4035_, v___x_4042_);
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 1, v___x_4043_);
                    lean_ctor_set(v___x_4013_, 0, v_toSnapshot_4030_);
                    v___x_4045_ = v___x_4013_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_toSnapshot_4030_);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4043_);
                    v___x_4045_ = v_reuseFailAlloc_4060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_snaps_4046_ = l_Lean_Language_SnapshotTree_getAll(v___x_4045_);
                v___x_4047_ = lean_unsigned_to_nat(0);
                v___x_4048_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
                v___x_4049_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once), _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3);
                v_sz_4050_ = lean_array_size(v_snaps_4046_);
                v___x_4051_ = 0usize;
                v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_4050_, v___x_4051_, v_snaps_4046_);
                v___x_4053_ = lean_array_get_size(v___x_4052_);
                v___x_4054_ = lean_nat_dec_lt(v___x_4047_, v___x_4053_);
                if v___x_4054_ == 0 {
                    lean_dec_ref(v___x_4052_);
                    v_unreported_4020_ = v___x_4048_;
                    state = 2;
                    continue;
                } else {
                    v___x_4055_ = lean_nat_dec_le(v___x_4053_, v___x_4053_);
                    if v___x_4055_ == 0 {
                        if v___x_4054_ == 0 {
                            lean_dec_ref(v___x_4052_);
                            v_unreported_4020_ = v___x_4048_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4056_ = lean_usize_of_nat(v___x_4053_);
                            v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4056_, v___x_4049_);
                            lean_dec_ref(v___x_4052_);
                            v___y_4028_ = v___x_4057_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4058_ = lean_usize_of_nat(v___x_4053_);
                        v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_4052_, v___x_4051_, v___x_4058_, v___x_4049_);
                        lean_dec_ref(v___x_4052_);
                        v___y_4028_ = v___x_4059_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                v_processedSnap_4066_ = lean_ctor_get(v_val_4062_, 1);
                lean_inc_ref(v_processedSnap_4066_);
                lean_dec(v_val_4062_);
                v_stx_x3f_4067_ = lean_ctor_get(v_processedSnap_4066_, 0);
                lean_inc(v_stx_x3f_4067_);
                v_reportingRange_4068_ = lean_ctor_get(v_processedSnap_4066_, 1);
                lean_inc(v_reportingRange_4068_);
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
                    lean_ctor_set(v___x_4064_, 0, v___x_4071_);
                    v___x_4073_ = v___x_4064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
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
    mut v_doc_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4080_: *mut LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(v_doc_4078_);
    return v_res_4080_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(
    mut v_as_4081_: *mut LeanObject,
    mut v_as_x27_4082_: *mut LeanObject,
    mut v_b_4083_: *mut LeanObject,
    mut v_a_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_4081_, v_as_x27_4082_, v_b_4083_);
    return v___x_4086_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(
    mut v_as_4087_: *mut LeanObject,
    mut v_as_x27_4088_: *mut LeanObject,
    mut v_b_4089_: *mut LeanObject,
    mut v_a_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4092_: *mut LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(v_as_4087_, v_as_x27_4088_, v_b_4089_, v_a_4090_);
    lean_dec(v_as_x27_4088_);
    lean_dec(v_as_4087_);
    return v_res_4092_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(
    mut v_as_4093_: *mut LeanObject,
    mut v_as_x27_4094_: *mut LeanObject,
    mut v_b_4095_: *mut LeanObject,
    mut v_a_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_4094_, v_b_4095_);
    return v___x_4098_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(
    mut v_as_4099_: *mut LeanObject,
    mut v_as_x27_4100_: *mut LeanObject,
    mut v_b_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4104_: *mut LeanObject = core::ptr::null_mut();
    v_res_4104_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(v_as_4099_, v_as_x27_4100_, v_b_4101_, v_a_4102_);
    lean_dec(v_as_x27_4100_);
    lean_dec(v_as_4099_);
    return v_res_4104_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
    mut v_a_4105_: *mut LeanObject,
    mut v_a_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ns_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_except_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4123_: u8 = 0;
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_id_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4105_) == 0 {
                    v___x_4107_ = l_List_reverse___redArg(v_a_4106_);
                    return v___x_4107_;
                } else {
                    v_head_4108_ = lean_ctor_get(v_a_4105_, 0);
                    v_tail_4109_ = lean_ctor_get(v_a_4105_, 1);
                    v_isSharedCheck_4138_ = (!lean_is_exclusive(v_a_4105_)) as u8;
                    if v_isSharedCheck_4138_ == 0 {
                        v___x_4111_ = v_a_4105_;
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4109_);
                        lean_inc(v_head_4108_);
                        lean_dec(v_a_4105_);
                        v___x_4111_ = lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4138_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_head_4108_) == 0 {
                    v_ns_4119_ = lean_ctor_get(v_head_4108_, 0);
                    v_except_4120_ = lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4128_ = (!lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4122_ = v_head_4108_;
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_except_4120_);
                        lean_inc(v_ns_4119_);
                        lean_dec(v_head_4108_);
                        v___x_4122_ = lean_box(0);
                        v_isShared_4123_ = v_isSharedCheck_4128_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_id_4129_ = lean_ctor_get(v_head_4108_, 0);
                    v_declName_4130_ = lean_ctor_get(v_head_4108_, 1);
                    v_isSharedCheck_4137_ = (!lean_is_exclusive(v_head_4108_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4132_ = v_head_4108_;
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_declName_4130_);
                        lean_inc(v_id_4129_);
                        lean_dec(v_head_4108_);
                        v___x_4132_ = lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4112_ == 0 {
                    lean_ctor_set(v___x_4111_, 1, v_a_4106_);
                    lean_ctor_set(v___x_4111_, 0, v___y_4114_);
                    v___x_4116_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___y_4114_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_a_4106_);
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
                    lean_ctor_set(v___x_4122_, 1, v___x_4124_);
                    v___x_4126_ = v___x_4122_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_ns_4119_);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4124_);
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
                    lean_ctor_set(v___x_4132_, 1, v_id_4129_);
                    lean_ctor_set(v___x_4132_, 0, v_declName_4130_);
                    v___x_4135_ = v___x_4132_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_declName_4130_);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_id_4129_);
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
    mut v_a_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4142_ = lean_ctor_get(v_a_4141_, 0);
                v_snd_4143_ = lean_ctor_get(v_a_4141_, 1);
                v_isSharedCheck_4159_ = (!lean_is_exclusive(v_a_4141_)) as u8;
                if v_isSharedCheck_4159_ == 0 {
                    v___x_4145_ = v_a_4141_;
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4143_);
                    lean_inc(v_fst_4142_);
                    lean_dec(v_a_4141_);
                    v___x_4145_ = lean_box(0);
                    v_isShared_4146_ = v_isSharedCheck_4159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4147_ = l_Lean_Name_isAnonymous(v_snd_4143_);
                if v___x_4147_ == 0 {
                    v___x_4148_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    lean_inc(v_snd_4143_);
                    v___x_4149_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4149_, 0, v_snd_4143_);
                    lean_ctor_set(v___x_4149_, 1, v___x_4148_);
                    v___x_4150_ = lean_array_push(v_fst_4142_, v___x_4149_);
                    v___x_4151_ = l_Lean_Name_getPrefix(v_snd_4143_);
                    lean_dec(v_snd_4143_);
                    if v_isShared_4146_ == 0 {
                        lean_ctor_set(v___x_4145_, 1, v___x_4151_);
                        lean_ctor_set(v___x_4145_, 0, v___x_4150_);
                        v___x_4153_ = v___x_4145_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4150_);
                        lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4151_);
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
                        v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_fst_4142_);
                        lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_snd_4143_);
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
    mut v_currentNamespace_4162_: *mut LeanObject,
    mut v_openDecls_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_openNamespaces_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    v_openNamespaces_4164_ = l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0;
    v___x_4165_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4165_, 0, v_openNamespaces_4164_);
    lean_ctor_set(v___x_4165_, 1, v_currentNamespace_4162_);
    v___x_4166_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v___x_4165_);
    v_fst_4167_ = lean_ctor_get(v___x_4166_, 0);
    lean_inc(v_fst_4167_);
    lean_dec_ref(v___x_4166_);
    v___x_4168_ = lean_box(0);
    v___x_4169_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(
        v_openDecls_4163_,
        v___x_4168_,
    );
    v___x_4170_ = lean_array_mk(v___x_4169_);
    v___x_4171_ = l_Array_append___redArg(v_fst_4167_, v___x_4170_);
    lean_dec_ref(v___x_4170_);
    return v___x_4171_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(
    mut v_inst_4172_: *mut LeanObject,
    mut v_a_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4174_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v_a_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
    mut v_doc_4175_: *mut LeanObject,
    mut v_currNamespace_4176_: *mut LeanObject,
    mut v_openDecls_4177_: *mut LeanObject,
    mut v_val_4178_: *mut LeanObject,
    mut v_val_4179_: *mut LeanObject,
    mut v___x_4180_: u8,
    mut v_decl_4181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEditableDocumentCore_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v_meta_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v_text_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minimizedId_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_unused_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4206_: u8 = 0;
    let mut v_unused_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4182_ = lean_ctor_get(v_doc_4175_, 0);
                v_isSharedCheck_4206_ = (!lean_is_exclusive(v_doc_4175_)) as u8;
                if v_isSharedCheck_4206_ == 0 {
                    v_unused_4207_ = lean_ctor_get(v_doc_4175_, 1);
                    lean_dec(v_unused_4207_);
                    v___x_4184_ = v_doc_4175_;
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toEditableDocumentCore_4182_);
                    lean_dec(v_doc_4175_);
                    v___x_4184_ = lean_box(0);
                    v_isShared_4185_ = v_isSharedCheck_4206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4186_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 0);
                v_isSharedCheck_4202_ = (!lean_is_exclusive(v_toEditableDocumentCore_4182_)) as u8;
                if v_isSharedCheck_4202_ == 0 {
                    v_unused_4203_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 3);
                    lean_dec(v_unused_4203_);
                    v_unused_4204_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 2);
                    lean_dec(v_unused_4204_);
                    v_unused_4205_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 1);
                    lean_dec(v_unused_4205_);
                    v___x_4188_ = v_toEditableDocumentCore_4182_;
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_meta_4186_);
                    lean_dec(v_toEditableDocumentCore_4182_);
                    v___x_4188_ = lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4190_ = lean_ctor_get(v_meta_4186_, 3);
                lean_inc_ref(v_text_4190_);
                lean_dec_ref(v_meta_4186_);
                v_minimizedId_4191_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(
                    v_currNamespace_4176_,
                    v_openDecls_4177_,
                    v_decl_4181_,
                );
                if v_isShared_4185_ == 0 {
                    lean_ctor_set(v___x_4184_, 1, v_val_4179_);
                    lean_ctor_set(v___x_4184_, 0, v_val_4178_);
                    v___x_4193_ = v___x_4184_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4178_);
                    lean_ctor_set(v_reuseFailAlloc_4201_, 1, v_val_4179_);
                    v___x_4193_ = v_reuseFailAlloc_4201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4194_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4190_, v___x_4193_);
                lean_inc(v_minimizedId_4191_);
                v___x_4195_ = l_Lean_Name_toString(v_minimizedId_4191_, v___x_4180_);
                v___x_4196_ = lean_box(0);
                if v_isShared_4189_ == 0 {
                    lean_ctor_set(v___x_4188_, 3, v___x_4196_);
                    lean_ctor_set(v___x_4188_, 2, v___x_4196_);
                    lean_ctor_set(v___x_4188_, 1, v___x_4195_);
                    lean_ctor_set(v___x_4188_, 0, v___x_4194_);
                    v___x_4198_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4195_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 2, v___x_4196_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 3, v___x_4196_);
                    v___x_4198_ = v_reuseFailAlloc_4200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4199_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4199_, 0, v_minimizedId_4191_);
                lean_ctor_set(v___x_4199_, 1, v___x_4198_);
                return v___x_4199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(
    mut v_doc_4208_: *mut LeanObject,
    mut v_currNamespace_4209_: *mut LeanObject,
    mut v_openDecls_4210_: *mut LeanObject,
    mut v_val_4211_: *mut LeanObject,
    mut v_val_4212_: *mut LeanObject,
    mut v___x_4213_: *mut LeanObject,
    mut v_decl_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_172__boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut LeanObject = core::ptr::null_mut();
    v___x_172__boxed_4215_ = (lean_unbox(v___x_4213_) as u8);
    v_res_4216_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(
        v_doc_4208_,
        v_currNamespace_4209_,
        v_openDecls_4210_,
        v_val_4211_,
        v_val_4212_,
        v___x_172__boxed_4215_,
        v_decl_4214_,
    );
    lean_dec(v_openDecls_4210_);
    return v_res_4216_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeIdQuery_x3f(
    mut v_doc_4217_: *mut LeanObject,
    mut v_ctx_4218_: *mut LeanObject,
    mut v_stx_4219_: *mut LeanObject,
    mut v_id_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v_currNamespace_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = 1;
                v___x_4222_ = l_Lean_Syntax_getPos_x3f(v_stx_4219_, v___x_4221_);
                if lean_obj_tag(v___x_4222_) == 1 {
                    v_val_4223_ = lean_ctor_get(v___x_4222_, 0);
                    lean_inc(v_val_4223_);
                    lean_dec_ref_known(v___x_4222_, 1);
                    v___x_4224_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4219_, v___x_4221_);
                    if lean_obj_tag(v___x_4224_) == 1 {
                        v_toCommandContextInfo_4225_ = lean_ctor_get(v_ctx_4218_, 0);
                        v_val_4226_ = lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4241_ = (!lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4241_ == 0 {
                            v___x_4228_ = v___x_4224_;
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_4226_);
                            lean_dec(v___x_4224_);
                            v___x_4228_ = lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4241_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4224_);
                        lean_dec(v_val_4223_);
                        lean_dec(v_id_4220_);
                        lean_dec_ref(v_ctx_4218_);
                        lean_dec_ref(v_doc_4217_);
                        v___x_4242_ = lean_box(0);
                        return v___x_4242_;
                    }
                } else {
                    lean_dec(v___x_4222_);
                    lean_dec(v_id_4220_);
                    lean_dec_ref(v_ctx_4218_);
                    lean_dec_ref(v_doc_4217_);
                    v___x_4243_ = lean_box(0);
                    return v___x_4243_;
                }
            }
            1 => {
                v_currNamespace_4230_ = lean_ctor_get(v_toCommandContextInfo_4225_, 5);
                v_openDecls_4231_ = lean_ctor_get(v_toCommandContextInfo_4225_, 6);
                v___x_4232_ = l_Lean_Name_toString(v_id_4220_, v___x_4221_);
                v___x_4233_ = lean_box((v___x_4221_) as usize);
                lean_inc_n(v_openDecls_4231_, 2);
                lean_inc_n(v_currNamespace_4230_, 2);
                v___f_4234_ = lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                lean_closure_set(v___f_4234_, 0, v_doc_4217_);
                lean_closure_set(v___f_4234_, 1, v_currNamespace_4230_);
                lean_closure_set(v___f_4234_, 2, v_openDecls_4231_);
                lean_closure_set(v___f_4234_, 3, v_val_4223_);
                lean_closure_set(v___f_4234_, 4, v_val_4226_);
                lean_closure_set(v___f_4234_, 5, v___x_4233_);
                v___x_4235_ = l_Lean_Server_FileWorker_collectOpenNamespaces(
                    v_currNamespace_4230_,
                    v_openDecls_4231_,
                );
                v___x_4236_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4236_, 0, v___x_4232_);
                lean_ctor_set(v___x_4236_, 1, v___x_4235_);
                v___x_4237_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                lean_ctor_set(v___x_4237_, 1, v_ctx_4218_);
                lean_ctor_set(v___x_4237_, 2, v___f_4234_);
                if v_isShared_4229_ == 0 {
                    lean_ctor_set(v___x_4228_, 0, v___x_4237_);
                    v___x_4239_ = v___x_4228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
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
    mut v_doc_4244_: *mut LeanObject,
    mut v_ctx_4245_: *mut LeanObject,
    mut v_stx_4246_: *mut LeanObject,
    mut v_id_4247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4248_: *mut LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(
        v_doc_4244_,
        v_ctx_4245_,
        v_stx_4246_,
        v_id_4247_,
    );
    lean_dec(v_stx_4246_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(
    mut v_e_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4252_ = l_Lean_Expr_hasMVar(v_e_4249_);
                if v___x_4252_ == 0 {
                    v___x_4253_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4253_, 0, v_e_4249_);
                    return v___x_4253_;
                } else {
                    v___x_4254_ = lean_st_ref_get(v___y_4250_);
                    v_mctx_4255_ = lean_ctor_get(v___x_4254_, 0);
                    lean_inc_ref(v_mctx_4255_);
                    lean_dec(v___x_4254_);
                    v___x_4256_ = l_Lean_instantiateMVarsCore(v_mctx_4255_, v_e_4249_);
                    v_fst_4257_ = lean_ctor_get(v___x_4256_, 0);
                    lean_inc(v_fst_4257_);
                    v_snd_4258_ = lean_ctor_get(v___x_4256_, 1);
                    lean_inc(v_snd_4258_);
                    lean_dec_ref(v___x_4256_);
                    v___x_4259_ = lean_st_ref_take(v___y_4250_);
                    v_cache_4260_ = lean_ctor_get(v___x_4259_, 1);
                    v_zetaDeltaFVarIds_4261_ = lean_ctor_get(v___x_4259_, 2);
                    v_postponed_4262_ = lean_ctor_get(v___x_4259_, 3);
                    v_diag_4263_ = lean_ctor_get(v___x_4259_, 4);
                    v_isSharedCheck_4272_ = (!lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4272_ == 0 {
                        v_unused_4273_ = lean_ctor_get(v___x_4259_, 0);
                        lean_dec(v_unused_4273_);
                        v___x_4265_ = v___x_4259_;
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4263_);
                        lean_inc(v_postponed_4262_);
                        lean_inc(v_zetaDeltaFVarIds_4261_);
                        lean_inc(v_cache_4260_);
                        lean_dec(v___x_4259_);
                        v___x_4265_ = lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4272_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4266_ == 0 {
                    lean_ctor_set(v___x_4265_, 0, v_snd_4258_);
                    v___x_4268_ = v___x_4265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_snd_4258_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_cache_4260_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_zetaDeltaFVarIds_4261_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_postponed_4262_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_diag_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4269_ = lean_st_ref_set(v___y_4250_, v___x_4268_);
                v___x_4270_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4270_, 0, v_fst_4257_);
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(
    mut v_e_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4277_: *mut LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4274_, v___y_4275_);
    lean_dec(v___y_4275_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
    mut v_e_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4284_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_4278_, v___y_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(
    mut v_e_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4291_: *mut LeanObject = core::ptr::null_mut();
    v_res_4291_ =
        l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(
            v_e_4285_,
            v___y_4286_,
            v___y_4287_,
            v___y_4288_,
            v___y_4289_,
        );
    lean_dec(v___y_4289_);
    lean_dec_ref(v___y_4288_);
    lean_dec(v___y_4287_);
    lean_dec_ref(v___y_4286_);
    return v_res_4291_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(
    mut v_expr_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v_a_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4296_);
                lean_inc_ref(v___y_4295_);
                lean_inc(v___y_4294_);
                lean_inc_ref(v___y_4293_);
                v___x_4308_ = lean_infer_type(
                    v_expr_4292_,
                    v___y_4293_,
                    v___y_4294_,
                    v___y_4295_,
                    v___y_4296_,
                );
                if lean_obj_tag(v___x_4308_) == 0 {
                    v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
                    lean_inc(v_a_4309_);
                    lean_dec_ref_known(v___x_4308_, 1);
                    v___x_4310_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_4309_, v___y_4294_);
                    v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4328_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4313_ = v___x_4310_;
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4311_);
                        lean_dec(v___x_4310_);
                        v___x_4313_ = lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___y_4296_);
                    lean_dec_ref(v___y_4295_);
                    lean_dec(v___y_4294_);
                    lean_dec_ref(v___y_4293_);
                    v_a_4329_ = lean_ctor_get(v___x_4308_, 0);
                    lean_inc(v_a_4329_);
                    lean_dec_ref_known(v___x_4308_, 1);
                    v_a_4305_ = v_a_4329_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_4300_ == 0 {
                    lean_dec_ref(v___y_4299_);
                    v___x_4301_ = lean_box(0);
                    v___x_4302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4302_, 0, v___x_4301_);
                    return v___x_4302_;
                } else {
                    v___x_4303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4303_, 0, v___y_4299_);
                    return v___x_4303_;
                }
            }
            2 => {
                v___x_4306_ = l_Lean_Exception_isInterrupt(v_a_4305_);
                if v___x_4306_ == 0 {
                    lean_inc_ref(v_a_4305_);
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
                lean_dec(v___y_4296_);
                lean_dec_ref(v___y_4295_);
                lean_dec(v___y_4294_);
                lean_dec_ref(v___y_4293_);
                if lean_obj_tag(v___x_4315_) == 0 {
                    v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4326_ = (!lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4318_ = v___x_4315_;
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4316_);
                        lean_dec(v___x_4315_);
                        v___x_4318_ = lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4326_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4313_);
                    v_a_4327_ = lean_ctor_get(v___x_4315_, 0);
                    lean_inc(v_a_4327_);
                    lean_dec_ref_known(v___x_4315_, 1);
                    v_a_4305_ = v_a_4327_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_4314_ == 0 {
                    lean_ctor_set_tag(v___x_4313_, 1);
                    lean_ctor_set(v___x_4313_, 0, v_a_4316_);
                    v___x_4321_ = v___x_4313_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4319_ == 0 {
                    lean_ctor_set(v___x_4318_, 0, v___x_4321_);
                    v___x_4323_ = v___x_4318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
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
    mut v_expr_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4336_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_val_4337_: *mut LeanObject,
    mut v_val_4338_: *mut LeanObject,
    mut v_text_4339_: *mut LeanObject,
    mut v_decl_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    v___x_4341_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4341_, 0, v_val_4337_);
    lean_ctor_set(v___x_4341_, 1, v_val_4338_);
    v___x_4342_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4339_, v___x_4341_);
    v___x_4343_ = l_Lean_Name_getString_x21(v_decl_4340_);
    v___x_4344_ = lean_box(0);
    v___x_4345_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4345_, 0, v___x_4342_);
    lean_ctor_set(v___x_4345_, 1, v___x_4343_);
    lean_ctor_set(v___x_4345_, 2, v___x_4344_);
    lean_ctor_set(v___x_4345_, 3, v___x_4344_);
    v___x_4346_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4346_, 0, v_decl_4340_);
    lean_ctor_set(v___x_4346_, 1, v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(
    mut v_sz_4347_: usize,
    mut v_i_4348_: usize,
    mut v_bs_4349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4350_: u8 = 0;
    let mut v_v_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: usize = 0;
    let mut v___x_4357_: usize = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4350_ = lean_usize_dec_lt(v_i_4348_, v_sz_4347_);
                if v___x_4350_ == 0 {
                    return v_bs_4349_;
                } else {
                    v_v_4351_ = lean_array_uget(v_bs_4349_, v_i_4348_);
                    v___x_4352_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4353_ = lean_array_uset(v_bs_4349_, v_i_4348_, v___x_4352_);
                    v___x_4354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0;
                    v___x_4355_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4355_, 0, v_v_4351_);
                    lean_ctor_set(v___x_4355_, 1, v___x_4354_);
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
    mut v_sz_4360_: *mut LeanObject,
    mut v_i_4361_: *mut LeanObject,
    mut v_bs_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4363_: usize = 0;
    let mut v_i_boxed_4364_: usize = 0;
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4363_ = lean_unbox_usize(v_sz_4360_);
    lean_dec(v_sz_4360_);
    v_i_boxed_4364_ = lean_unbox_usize(v_i_4361_);
    lean_dec(v_i_4361_);
    v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_4363_, v_i_boxed_4364_, v_bs_4362_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotQuery_x3f(
    mut v_doc_4366_: *mut LeanObject,
    mut v_ctx_4367_: *mut LeanObject,
    mut v_ti_4368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toElabInfo_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v_val_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v_toEditableDocumentCore_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_meta_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4404_: usize = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_unused_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toElabInfo_4370_ = lean_ctor_get(v_ti_4368_, 0);
                lean_inc_ref(v_toElabInfo_4370_);
                v_lctx_4371_ = lean_ctor_get(v_ti_4368_, 1);
                lean_inc_ref(v_lctx_4371_);
                v_expr_4372_ = lean_ctor_get(v_ti_4368_, 3);
                lean_inc_ref(v_expr_4372_);
                lean_dec_ref(v_ti_4368_);
                v_stx_4373_ = lean_ctor_get(v_toElabInfo_4370_, 1);
                lean_inc(v_stx_4373_);
                lean_dec_ref(v_toElabInfo_4370_);
                v___x_4374_ = 1;
                v___x_4375_ = l_Lean_Syntax_getPos_x3f(v_stx_4373_, v___x_4374_);
                if lean_obj_tag(v___x_4375_) == 1 {
                    v_val_4376_ = lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4441_ = (!lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4441_ == 0 {
                        v___x_4378_ = v___x_4375_;
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4376_);
                        lean_dec(v___x_4375_);
                        v___x_4378_ = lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4441_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4375_);
                    lean_dec(v_stx_4373_);
                    lean_dec_ref(v_expr_4372_);
                    lean_dec_ref(v_lctx_4371_);
                    lean_dec_ref(v_ctx_4367_);
                    lean_dec_ref(v_doc_4366_);
                    v___x_4442_ = lean_box(0);
                    v___x_4443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4443_, 0, v___x_4442_);
                    return v___x_4443_;
                }
            }
            1 => {
                v___x_4380_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4373_, v___x_4374_);
                lean_dec(v_stx_4373_);
                if lean_obj_tag(v___x_4380_) == 1 {
                    lean_del_object(v___x_4378_);
                    v_val_4381_ = lean_ctor_get(v___x_4380_, 0);
                    lean_inc(v_val_4381_);
                    lean_dec_ref_known(v___x_4380_, 1);
                    v___f_4382_ = lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___f_4382_, 0, v_expr_4372_);
                    lean_inc_ref(v_ctx_4367_);
                    v___x_4383_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_4367_,
                        v_lctx_4371_,
                        v___f_4382_,
                    );
                    if lean_obj_tag(v___x_4383_) == 0 {
                        v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4428_ = (!lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4386_ = v___x_4383_;
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4384_);
                            lean_dec(v___x_4383_);
                            v___x_4386_ = lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4428_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_4381_);
                        lean_dec(v_val_4376_);
                        lean_dec_ref(v_ctx_4367_);
                        lean_dec_ref(v_doc_4366_);
                        v_a_4429_ = lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4436_ = (!lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4436_ == 0 {
                            v___x_4431_ = v___x_4383_;
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4429_);
                            lean_dec(v___x_4383_);
                            v___x_4431_ = lean_box(0);
                            v_isShared_4432_ = v_isSharedCheck_4436_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4380_);
                    lean_dec(v_val_4376_);
                    lean_dec_ref(v_expr_4372_);
                    lean_dec_ref(v_lctx_4371_);
                    lean_dec_ref(v_ctx_4367_);
                    lean_dec_ref(v_doc_4366_);
                    v___x_4437_ = lean_box(0);
                    if v_isShared_4379_ == 0 {
                        lean_ctor_set_tag(v___x_4378_, 0);
                        lean_ctor_set(v___x_4378_, 0, v___x_4437_);
                        v___x_4439_ = v___x_4378_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
                        v___x_4439_ = v_reuseFailAlloc_4440_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4384_) == 1 {
                    v_val_4388_ = lean_ctor_get(v_a_4384_, 0);
                    v_isSharedCheck_4423_ = (!lean_is_exclusive(v_a_4384_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4390_ = v_a_4384_;
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4388_);
                        lean_dec(v_a_4384_);
                        v___x_4390_ = lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4423_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4384_);
                    lean_dec(v_val_4381_);
                    lean_dec(v_val_4376_);
                    lean_dec_ref(v_ctx_4367_);
                    lean_dec_ref(v_doc_4366_);
                    v___x_4424_ = lean_box(0);
                    if v_isShared_4387_ == 0 {
                        lean_ctor_set(v___x_4386_, 0, v___x_4424_);
                        v___x_4426_ = v___x_4386_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
                        v___x_4426_ = v_reuseFailAlloc_4427_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4392_ = lean_array_get_size(v_val_4388_);
                v___x_4393_ = lean_unsigned_to_nat(0);
                v___x_4394_ = lean_nat_dec_eq(v___x_4392_, v___x_4393_);
                if v___x_4394_ == 0 {
                    v_toEditableDocumentCore_4395_ = lean_ctor_get(v_doc_4366_, 0);
                    v_isSharedCheck_4417_ = (!lean_is_exclusive(v_doc_4366_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v_unused_4418_ = lean_ctor_get(v_doc_4366_, 1);
                        lean_dec(v_unused_4418_);
                        v___x_4397_ = v_doc_4366_;
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_toEditableDocumentCore_4395_);
                        lean_dec(v_doc_4366_);
                        v___x_4397_ = lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4417_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4390_);
                    lean_dec(v_val_4388_);
                    lean_dec(v_val_4381_);
                    lean_dec(v_val_4376_);
                    lean_dec_ref(v_ctx_4367_);
                    lean_dec_ref(v_doc_4366_);
                    v___x_4419_ = lean_box(0);
                    if v_isShared_4387_ == 0 {
                        lean_ctor_set(v___x_4386_, 0, v___x_4419_);
                        v___x_4421_ = v___x_4386_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_meta_4399_ = lean_ctor_get(v_toEditableDocumentCore_4395_, 0);
                lean_inc_ref(v_meta_4399_);
                lean_dec_ref(v_toEditableDocumentCore_4395_);
                v_text_4400_ = lean_ctor_get(v_meta_4399_, 3);
                lean_inc_ref(v_text_4400_);
                lean_dec_ref(v_meta_4399_);
                v_source_4401_ = lean_ctor_get(v_text_4400_, 0);
                lean_inc_ref(v_source_4401_);
                lean_inc(v_val_4381_);
                lean_inc(v_val_4376_);
                v___f_4402_ = lean_alloc_closure(
                    l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4402_, 0, v_val_4376_);
                lean_closure_set(v___f_4402_, 1, v_val_4381_);
                lean_closure_set(v___f_4402_, 2, v_text_4400_);
                v___x_4403_ = lean_string_utf8_extract(v_source_4401_, v_val_4376_, v_val_4381_);
                lean_dec(v_val_4381_);
                lean_dec(v_val_4376_);
                lean_dec_ref(v_source_4401_);
                v_sz_4404_ = lean_array_size(v_val_4388_);
                v___x_4405_ = 0usize;
                v___x_4406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4404_, v___x_4405_, v_val_4388_);
                if v_isShared_4398_ == 0 {
                    lean_ctor_set(v___x_4397_, 1, v___x_4406_);
                    lean_ctor_set(v___x_4397_, 0, v___x_4403_);
                    v___x_4408_ = v___x_4397_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4403_);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4406_);
                    v___x_4408_ = v_reuseFailAlloc_4416_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4409_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4409_, 0, v___x_4408_);
                lean_ctor_set(v___x_4409_, 1, v_ctx_4367_);
                lean_ctor_set(v___x_4409_, 2, v___f_4402_);
                if v_isShared_4391_ == 0 {
                    lean_ctor_set(v___x_4390_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4390_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4415_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4387_ == 0 {
                    lean_ctor_set(v___x_4386_, 0, v___x_4411_);
                    v___x_4413_ = v___x_4386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
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
                    v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
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
    mut v_doc_4444_: *mut LeanObject,
    mut v_ctx_4445_: *mut LeanObject,
    mut v_ti_4446_: *mut LeanObject,
    mut v_a_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4448_: *mut LeanObject = core::ptr::null_mut();
    v_res_4448_ =
        l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_4444_, v_ctx_4445_, v_ti_4446_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(
    mut v_doc_4449_: *mut LeanObject,
    mut v_val_4450_: *mut LeanObject,
    mut v_val_4451_: *mut LeanObject,
    mut v_decl_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEditableDocumentCore_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v_meta_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4460_: u8 = 0;
    let mut v_text_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_unused_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_unused_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_4453_ = lean_ctor_get(v_doc_4449_, 0);
                v_isSharedCheck_4476_ = (!lean_is_exclusive(v_doc_4449_)) as u8;
                if v_isSharedCheck_4476_ == 0 {
                    v_unused_4477_ = lean_ctor_get(v_doc_4449_, 1);
                    lean_dec(v_unused_4477_);
                    v___x_4455_ = v_doc_4449_;
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toEditableDocumentCore_4453_);
                    lean_dec(v_doc_4449_);
                    v___x_4455_ = lean_box(0);
                    v_isShared_4456_ = v_isSharedCheck_4476_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_4457_ = lean_ctor_get(v_toEditableDocumentCore_4453_, 0);
                v_isSharedCheck_4472_ = (!lean_is_exclusive(v_toEditableDocumentCore_4453_)) as u8;
                if v_isSharedCheck_4472_ == 0 {
                    v_unused_4473_ = lean_ctor_get(v_toEditableDocumentCore_4453_, 3);
                    lean_dec(v_unused_4473_);
                    v_unused_4474_ = lean_ctor_get(v_toEditableDocumentCore_4453_, 2);
                    lean_dec(v_unused_4474_);
                    v_unused_4475_ = lean_ctor_get(v_toEditableDocumentCore_4453_, 1);
                    lean_dec(v_unused_4475_);
                    v___x_4459_ = v_toEditableDocumentCore_4453_;
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_meta_4457_);
                    lean_dec(v_toEditableDocumentCore_4453_);
                    v___x_4459_ = lean_box(0);
                    v_isShared_4460_ = v_isSharedCheck_4472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_text_4461_ = lean_ctor_get(v_meta_4457_, 3);
                lean_inc_ref(v_text_4461_);
                lean_dec_ref(v_meta_4457_);
                if v_isShared_4456_ == 0 {
                    lean_ctor_set(v___x_4455_, 1, v_val_4451_);
                    lean_ctor_set(v___x_4455_, 0, v_val_4450_);
                    v___x_4463_ = v___x_4455_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_val_4450_);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_val_4451_);
                    v___x_4463_ = v_reuseFailAlloc_4471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4464_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4461_, v___x_4463_);
                v___x_4465_ = l_Lean_Name_getString_x21(v_decl_4452_);
                v___x_4466_ = lean_box(0);
                if v_isShared_4460_ == 0 {
                    lean_ctor_set(v___x_4459_, 3, v___x_4466_);
                    lean_ctor_set(v___x_4459_, 2, v___x_4466_);
                    lean_ctor_set(v___x_4459_, 1, v___x_4465_);
                    lean_ctor_set(v___x_4459_, 0, v___x_4464_);
                    v___x_4468_ = v___x_4459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4464_);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4465_);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 2, v___x_4466_);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 3, v___x_4466_);
                    v___x_4468_ = v_reuseFailAlloc_4470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4469_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4469_, 0, v_decl_4452_);
                lean_ctor_set(v___x_4469_, 1, v___x_4468_);
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
    mut v_doc_4478_: *mut LeanObject,
    mut v_ctx_4479_: *mut LeanObject,
    mut v_stx_4480_: *mut LeanObject,
    mut v_id_4481_: *mut LeanObject,
    mut v_lctx_4482_: *mut LeanObject,
    mut v_expectedType_x3f_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: u8 = 0;
    let mut v___f_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_unused_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ = 1;
                v___x_4486_ = l_Lean_Syntax_getPos_x3f(v_stx_4480_, v___x_4485_);
                if lean_obj_tag(v___x_4486_) == 1 {
                    v_val_4487_ = lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4546_ = (!lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4546_ == 0 {
                        v___x_4489_ = v___x_4486_;
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4487_);
                        lean_dec(v___x_4486_);
                        v___x_4489_ = lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4546_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4486_);
                    lean_dec(v_expectedType_x3f_4483_);
                    lean_dec_ref(v_lctx_4482_);
                    lean_dec(v_id_4481_);
                    lean_dec_ref(v_ctx_4479_);
                    lean_dec_ref(v_doc_4478_);
                    v___x_4547_ = lean_box(0);
                    v___x_4548_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4548_, 0, v___x_4547_);
                    return v___x_4548_;
                }
            }
            1 => {
                v___x_4491_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4480_, v___x_4485_);
                if lean_obj_tag(v___x_4491_) == 1 {
                    lean_del_object(v___x_4489_);
                    if lean_obj_tag(v_expectedType_x3f_4483_) == 1 {
                        v_val_4492_ = lean_ctor_get(v___x_4491_, 0);
                        lean_inc(v_val_4492_);
                        lean_dec_ref_known(v___x_4491_, 1);
                        v_val_4493_ = lean_ctor_get(v_expectedType_x3f_4483_, 0);
                        v_isSharedCheck_4532_ =
                            (!lean_is_exclusive(v_expectedType_x3f_4483_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4495_ = v_expectedType_x3f_4483_;
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_4493_);
                            lean_dec(v_expectedType_x3f_4483_);
                            v___x_4495_ = lean_box(0);
                            v_isShared_4496_ = v_isSharedCheck_4532_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_4487_);
                        lean_dec(v_expectedType_x3f_4483_);
                        lean_dec_ref(v_lctx_4482_);
                        lean_dec(v_id_4481_);
                        lean_dec_ref(v_ctx_4479_);
                        lean_dec_ref(v_doc_4478_);
                        v_isSharedCheck_4540_ = (!lean_is_exclusive(v___x_4491_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v_unused_4541_ = lean_ctor_get(v___x_4491_, 0);
                            lean_dec(v_unused_4541_);
                            v___x_4534_ = v___x_4491_;
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v___x_4491_);
                            v___x_4534_ = lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4491_);
                    lean_dec(v_val_4487_);
                    lean_dec(v_expectedType_x3f_4483_);
                    lean_dec_ref(v_lctx_4482_);
                    lean_dec(v_id_4481_);
                    lean_dec_ref(v_ctx_4479_);
                    lean_dec_ref(v_doc_4478_);
                    v___x_4542_ = lean_box(0);
                    if v_isShared_4490_ == 0 {
                        lean_ctor_set_tag(v___x_4489_, 0);
                        lean_ctor_set(v___x_4489_, 0, v___x_4542_);
                        v___x_4544_ = v___x_4489_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
                        v___x_4544_ = v_reuseFailAlloc_4545_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4497_ = lean_alloc_closure(
                    l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed
                        as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___x_4497_, 0, v_val_4493_);
                lean_inc_ref(v_ctx_4479_);
                v___x_4498_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                    v_ctx_4479_,
                    v_lctx_4482_,
                    v___x_4497_,
                );
                if lean_obj_tag(v___x_4498_) == 0 {
                    v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4523_ = (!lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4523_ == 0 {
                        v___x_4501_ = v___x_4498_;
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4499_);
                        lean_dec(v___x_4498_);
                        v___x_4501_ = lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4523_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4495_);
                    lean_dec(v_val_4492_);
                    lean_dec(v_val_4487_);
                    lean_dec(v_id_4481_);
                    lean_dec_ref(v_ctx_4479_);
                    lean_dec_ref(v_doc_4478_);
                    v_a_4524_ = lean_ctor_get(v___x_4498_, 0);
                    v_isSharedCheck_4531_ = (!lean_is_exclusive(v___x_4498_)) as u8;
                    if v_isSharedCheck_4531_ == 0 {
                        v___x_4526_ = v___x_4498_;
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4524_);
                        lean_dec(v___x_4498_);
                        v___x_4526_ = lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4503_ = lean_array_get_size(v_a_4499_);
                v___x_4504_ = lean_unsigned_to_nat(0);
                v___x_4505_ = lean_nat_dec_eq(v___x_4503_, v___x_4504_);
                if v___x_4505_ == 0 {
                    v___f_4506_ = lean_alloc_closure(
                        l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_4506_, 0, v_doc_4478_);
                    lean_closure_set(v___f_4506_, 1, v_val_4487_);
                    lean_closure_set(v___f_4506_, 2, v_val_4492_);
                    v___x_4507_ = l_Lean_Name_toString(v_id_4481_, v___x_4485_);
                    v_sz_4508_ = lean_array_size(v_a_4499_);
                    v___x_4509_ = 0usize;
                    v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_4508_, v___x_4509_, v_a_4499_);
                    v___x_4511_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4511_, 0, v___x_4507_);
                    lean_ctor_set(v___x_4511_, 1, v___x_4510_);
                    v___x_4512_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    lean_ctor_set(v___x_4512_, 1, v_ctx_4479_);
                    lean_ctor_set(v___x_4512_, 2, v___f_4506_);
                    if v_isShared_4496_ == 0 {
                        lean_ctor_set(v___x_4495_, 0, v___x_4512_);
                        v___x_4514_ = v___x_4495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4512_);
                        v___x_4514_ = v_reuseFailAlloc_4518_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4499_);
                    lean_del_object(v___x_4495_);
                    lean_dec(v_val_4492_);
                    lean_dec(v_val_4487_);
                    lean_dec(v_id_4481_);
                    lean_dec_ref(v_ctx_4479_);
                    lean_dec_ref(v_doc_4478_);
                    v___x_4519_ = lean_box(0);
                    if v_isShared_4502_ == 0 {
                        lean_ctor_set(v___x_4501_, 0, v___x_4519_);
                        v___x_4521_ = v___x_4501_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
                        v___x_4521_ = v_reuseFailAlloc_4522_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4502_ == 0 {
                    lean_ctor_set(v___x_4501_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4501_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
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
                    v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4529_;
            }
            9 => {
                v___x_4536_ = lean_box(0);
                if v_isShared_4535_ == 0 {
                    lean_ctor_set_tag(v___x_4534_, 0);
                    lean_ctor_set(v___x_4534_, 0, v___x_4536_);
                    v___x_4538_ = v___x_4534_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
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
    mut v_doc_4549_: *mut LeanObject,
    mut v_ctx_4550_: *mut LeanObject,
    mut v_stx_4551_: *mut LeanObject,
    mut v_id_4552_: *mut LeanObject,
    mut v_lctx_4553_: *mut LeanObject,
    mut v_expectedType_x3f_4554_: *mut LeanObject,
    mut v_a_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4556_: *mut LeanObject = core::ptr::null_mut();
    v_res_4556_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
        v_doc_4549_,
        v_ctx_4550_,
        v_stx_4551_,
        v_id_4552_,
        v_lctx_4553_,
        v_expectedType_x3f_4554_,
    );
    lean_dec(v_stx_4551_);
    return v_res_4556_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(
    mut v_doc_4557_: *mut LeanObject,
    mut v_as_4558_: *mut LeanObject,
    mut v_sz_4559_: usize,
    mut v_i_4560_: usize,
    mut v_b_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: usize = 0;
    let mut v_query_x3f_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termInfo_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_ctx_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4572_ = lean_usize_dec_lt(v_i_4560_, v_sz_4559_);
                if v___x_4572_ == 0 {
                    lean_dec_ref(v_doc_4557_);
                    v___x_4573_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4573_, 0, v_b_4561_);
                    return v___x_4573_;
                } else {
                    v_a_4574_ = lean_array_uget_borrowed(v_as_4558_, v_i_4560_);
                    v_fst_4575_ = lean_ctor_get(v_a_4574_, 0);
                    v_info_4576_ = lean_ctor_get(v_fst_4575_, 2);
                    match lean_obj_tag(v_info_4576_) {
                        1 => {
                            v_ctx_4577_ = lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4578_ = lean_ctor_get(v_info_4576_, 0);
                            v_id_4579_ = lean_ctor_get(v_info_4576_, 1);
                            lean_inc(v_id_4579_);
                            lean_inc_ref(v_ctx_4577_);
                            lean_inc_ref(v_doc_4557_);
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
                            v_ctx_4581_ = lean_ctor_get(v_fst_4575_, 1);
                            v_termInfo_4582_ = lean_ctor_get(v_info_4576_, 0);
                            lean_inc_ref(v_termInfo_4582_);
                            lean_inc_ref(v_ctx_4581_);
                            lean_inc_ref(v_doc_4557_);
                            v___x_4583_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4581_,
                                v_termInfo_4582_,
                            );
                            if lean_obj_tag(v___x_4583_) == 0 {
                                v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
                                lean_inc(v_a_4584_);
                                lean_dec_ref_known(v___x_4583_, 1);
                                v_query_x3f_4569_ = v_a_4584_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v_b_4561_);
                                lean_dec_ref(v_doc_4557_);
                                v_a_4585_ = lean_ctor_get(v___x_4583_, 0);
                                v_isSharedCheck_4593_ = (!lean_is_exclusive(v___x_4583_)) as u8;
                                if v_isSharedCheck_4593_ == 0 {
                                    v___x_4587_ = v___x_4583_;
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_4585_);
                                    lean_dec(v___x_4583_);
                                    v___x_4587_ = lean_box(0);
                                    v_isShared_4588_ = v_isSharedCheck_4593_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        2 => {
                            v_ctx_4594_ = lean_ctor_get(v_fst_4575_, 1);
                            v_stx_4595_ = lean_ctor_get(v_info_4576_, 0);
                            v_id_4596_ = lean_ctor_get(v_info_4576_, 1);
                            v_lctx_4597_ = lean_ctor_get(v_info_4576_, 2);
                            v_expectedType_x3f_4598_ = lean_ctor_get(v_info_4576_, 3);
                            lean_inc(v_expectedType_x3f_4598_);
                            lean_inc_ref(v_lctx_4597_);
                            lean_inc(v_id_4596_);
                            lean_inc_ref(v_ctx_4594_);
                            lean_inc_ref(v_doc_4557_);
                            v___x_4599_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(
                                v_doc_4557_,
                                v_ctx_4594_,
                                v_stx_4595_,
                                v_id_4596_,
                                v_lctx_4597_,
                                v_expectedType_x3f_4598_,
                            );
                            if lean_obj_tag(v___x_4599_) == 0 {
                                v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
                                lean_inc(v_a_4600_);
                                lean_dec_ref_known(v___x_4599_, 1);
                                v_query_x3f_4569_ = v_a_4600_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v_b_4561_);
                                lean_dec_ref(v_doc_4557_);
                                v_a_4601_ = lean_ctor_get(v___x_4599_, 0);
                                v_isSharedCheck_4609_ = (!lean_is_exclusive(v___x_4599_)) as u8;
                                if v_isSharedCheck_4609_ == 0 {
                                    v___x_4603_ = v___x_4599_;
                                    v_isShared_4604_ = v_isSharedCheck_4609_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_4601_);
                                    lean_dec(v___x_4599_);
                                    v___x_4603_ = lean_box(0);
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
                if lean_obj_tag(v_query_x3f_4569_) == 1 {
                    v_val_4570_ = lean_ctor_get(v_query_x3f_4569_, 0);
                    lean_inc(v_val_4570_);
                    lean_dec_ref_known(v_query_x3f_4569_, 1);
                    v___x_4571_ = lean_array_push(v_b_4561_, v_val_4570_);
                    v_a_4564_ = v___x_4571_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_query_x3f_4569_);
                    v_a_4564_ = v_b_4561_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4589_ = l_Lean_Server_RequestError_ofIoError(v_a_4585_);
                if v_isShared_4588_ == 0 {
                    lean_ctor_set(v___x_4587_, 0, v___x_4589_);
                    v___x_4591_ = v___x_4587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
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
                    lean_ctor_set(v___x_4603_, 0, v___x_4605_);
                    v___x_4607_ = v___x_4603_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
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
    mut v_doc_4610_: *mut LeanObject,
    mut v_as_4611_: *mut LeanObject,
    mut v_sz_4612_: *mut LeanObject,
    mut v_i_4613_: *mut LeanObject,
    mut v_b_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4616_: usize = 0;
    let mut v_i_boxed_4617_: usize = 0;
    let mut v_res_4618_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4616_ = lean_unbox_usize(v_sz_4612_);
    lean_dec(v_sz_4612_);
    v_i_boxed_4617_ = lean_unbox_usize(v_i_4613_);
    lean_dec(v_i_4613_);
    v_res_4618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4610_, v_as_4611_, v_sz_boxed_4616_, v_i_boxed_4617_, v_b_4614_);
    lean_dec_ref(v_as_4611_);
    return v_res_4618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(
    mut v_doc_4619_: *mut LeanObject,
    mut v_as_4620_: *mut LeanObject,
    mut v_sz_4621_: usize,
    mut v_i_4622_: usize,
    mut v_b_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: usize = 0;
    let mut v___x_4637_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4626_ = lean_usize_dec_lt(v_i_4622_, v_sz_4621_);
                if v___x_4626_ == 0 {
                    lean_dec_ref(v_doc_4619_);
                    v___x_4627_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4627_, 0, v_b_4623_);
                    return v___x_4627_;
                } else {
                    v_a_4628_ = lean_array_uget_borrowed(v_as_4620_, v_i_4622_);
                    v_sz_4629_ = lean_array_size(v_a_4628_);
                    v___x_4630_ = 0usize;
                    lean_inc_ref(v_doc_4619_);
                    v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4619_, v_a_4628_, v_sz_4629_, v___x_4630_, v_b_4623_);
                    if lean_obj_tag(v___x_4631_) == 0 {
                        v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
                        lean_inc(v_a_4632_);
                        v___x_4633_ = lean_array_get_size(v_a_4632_);
                        v___x_4634_ = lean_unsigned_to_nat(0);
                        v___x_4635_ = lean_nat_dec_eq(v___x_4633_, v___x_4634_);
                        if v___x_4635_ == 0 {
                            lean_dec(v_a_4632_);
                            lean_dec_ref(v_doc_4619_);
                            return v___x_4631_;
                        } else {
                            lean_dec_ref_known(v___x_4631_, 1);
                            v___x_4636_ = 1usize;
                            v___x_4637_ = lean_usize_add(v_i_4622_, v___x_4636_);
                            v_i_4622_ = v___x_4637_;
                            v_b_4623_ = v_a_4632_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_doc_4619_);
                        return v___x_4631_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(
    mut v_doc_4639_: *mut LeanObject,
    mut v_as_4640_: *mut LeanObject,
    mut v_sz_4641_: *mut LeanObject,
    mut v_i_4642_: *mut LeanObject,
    mut v_b_4643_: *mut LeanObject,
    mut v___y_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4646_: usize = 0;
    let mut v_i_boxed_4647_: usize = 0;
    let mut v_res_4648_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4646_ = lean_unbox_usize(v_sz_4641_);
    lean_dec(v_sz_4641_);
    v_i_boxed_4647_ = lean_unbox_usize(v_i_4642_);
    lean_dec(v_i_4642_);
    v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4639_, v_as_4640_, v_sz_boxed_4646_, v_i_boxed_4647_, v_b_4643_, v___y_4644_);
    lean_dec_ref(v___y_4644_);
    lean_dec_ref(v_as_4640_);
    return v_res_4648_;
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries(
    mut v_doc_4651_: *mut LeanObject,
    mut v_requestedPos_4652_: *mut LeanObject,
    mut v_a_4653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEditableDocumentCore_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_4655_ = lean_ctor_get(v_doc_4651_, 0);
    v___x_4656_ = 1;
    lean_inc(v_requestedPos_4652_);
    lean_inc_ref(v_doc_4651_);
    v___x_4657_ =
        l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_4651_, v_requestedPos_4652_, v___x_4656_);
    v___x_4658_ = lean_task_get_own(v___x_4657_);
    if lean_obj_tag(v___x_4658_) == 1 {
        let mut v_val_4659_: *mut LeanObject = core::ptr::null_mut();
        let mut v_meta_4660_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4661_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v_text_4663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4665_: *mut LeanObject = core::ptr::null_mut();
        let mut v_queries_4666_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4667_: usize = 0;
        let mut v___x_4668_: usize = 0;
        let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
        v_val_4659_ = lean_ctor_get(v___x_4658_, 0);
        lean_inc(v_val_4659_);
        lean_dec_ref_known(v___x_4658_, 1);
        v_meta_4660_ = lean_ctor_get(v_toEditableDocumentCore_4655_, 0);
        v_fst_4661_ = lean_ctor_get(v_val_4659_, 0);
        lean_inc(v_fst_4661_);
        v_snd_4662_ = lean_ctor_get(v_val_4659_, 1);
        lean_inc(v_snd_4662_);
        lean_dec(v_val_4659_);
        v_text_4663_ = lean_ctor_get(v_meta_4660_, 3);
        lean_inc_ref(v_text_4663_);
        v___x_4664_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
            v_text_4663_,
            v_requestedPos_4652_,
            v_fst_4661_,
            v_snd_4662_,
        );
        v_fst_4665_ = lean_ctor_get(v___x_4664_, 0);
        lean_inc(v_fst_4665_);
        lean_dec_ref(v___x_4664_);
        v_queries_4666_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v_sz_4667_ = lean_array_size(v_fst_4665_);
        v___x_4668_ = 0usize;
        v___x_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_4651_, v_fst_4665_, v_sz_4667_, v___x_4668_, v_queries_4666_, v_a_4653_);
        lean_dec(v_fst_4665_);
        return v___x_4669_;
    } else {
        let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_4658_);
        lean_dec(v_requestedPos_4652_);
        lean_dec_ref(v_doc_4651_);
        v___x_4670_ = l_Lean_Server_FileWorker_computeQueries___closed__0;
        v___x_4671_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4671_, 0, v___x_4670_);
        return v___x_4671_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_computeQueries___boxed(
    mut v_doc_4672_: *mut LeanObject,
    mut v_requestedPos_4673_: *mut LeanObject,
    mut v_a_4674_: *mut LeanObject,
    mut v_a_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4676_: *mut LeanObject = core::ptr::null_mut();
    v_res_4676_ =
        l_Lean_Server_FileWorker_computeQueries(v_doc_4672_, v_requestedPos_4673_, v_a_4674_);
    lean_dec_ref(v_a_4674_);
    return v_res_4676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(
    mut v_doc_4677_: *mut LeanObject,
    mut v_as_4678_: *mut LeanObject,
    mut v_sz_4679_: usize,
    mut v_i_4680_: usize,
    mut v_b_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_4677_, v_as_4678_, v_sz_4679_, v_i_4680_, v_b_4681_);
    return v___x_4684_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(
    mut v_doc_4685_: *mut LeanObject,
    mut v_as_4686_: *mut LeanObject,
    mut v_sz_4687_: *mut LeanObject,
    mut v_i_4688_: *mut LeanObject,
    mut v_b_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4692_: usize = 0;
    let mut v_i_boxed_4693_: usize = 0;
    let mut v_res_4694_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4692_ = lean_unbox_usize(v_sz_4687_);
    lean_dec(v_sz_4687_);
    v_i_boxed_4693_ = lean_unbox_usize(v_i_4688_);
    lean_dec(v_i_4688_);
    v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_4685_, v_as_4686_, v_sz_boxed_4692_, v_i_boxed_4693_, v_b_4689_, v___y_4690_);
    lean_dec_ref(v___y_4690_);
    lean_dec_ref(v_as_4686_);
    return v_res_4694_;
}
pub unsafe fn l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
    mut v_params_4703_: *mut LeanObject,
    mut v_name_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    v___x_4705_ = lean_unsigned_to_nat(0);
    v___x_4706_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4706_, 0, v_params_4703_);
    lean_ctor_set(v___x_4706_, 1, v_name_4704_);
    lean_ctor_set(v___x_4706_, 2, v___x_4705_);
    return v___x_4706_;
}
pub unsafe fn l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
    mut v_params_4708_: *mut LeanObject,
    mut v_kind_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    v___x_4710_ = lean_box(0);
    v___x_4711_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0;
    v___x_4712_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4712_, 0, v_kind_4709_);
    v___x_4713_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
    v___x_4714_ =
        l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_4708_, v___x_4713_);
    v___x_4715_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4714_);
    v___x_4716_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4716_, 0, v___x_4715_);
    v___x_4717_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4717_, 0, v___x_4710_);
    lean_ctor_set(v___x_4717_, 1, v___x_4710_);
    lean_ctor_set(v___x_4717_, 2, v___x_4711_);
    lean_ctor_set(v___x_4717_, 3, v___x_4712_);
    lean_ctor_set(v___x_4717_, 4, v___x_4710_);
    lean_ctor_set(v___x_4717_, 5, v___x_4710_);
    lean_ctor_set(v___x_4717_, 6, v___x_4710_);
    lean_ctor_set(v___x_4717_, 7, v___x_4710_);
    lean_ctor_set(v___x_4717_, 8, v___x_4710_);
    lean_ctor_set(v___x_4717_, 9, v___x_4716_);
    return v___x_4717_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(
    mut v_ctx_4722_: *mut LeanObject,
    mut v_mod_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommandContextInfo_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: u8 = 0;
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_4731_: *mut LeanObject = core::ptr::null_mut();
    v_toCommandContextInfo_4724_ = lean_ctor_get(v_ctx_4722_, 0);
    lean_inc_ref(v_toCommandContextInfo_4724_);
    v_parentDecl_x3f_4725_ = lean_ctor_get(v_ctx_4722_, 1);
    lean_inc(v_parentDecl_x3f_4725_);
    lean_dec_ref(v_ctx_4722_);
    v___x_4726_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0;
    v___x_4727_ = 1;
    v___x_4728_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4723_, v___x_4727_);
    v___x_4729_ = lean_string_append(v___x_4726_, v___x_4728_);
    lean_dec_ref(v___x_4728_);
    v___x_4730_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
    v_text_4731_ = lean_string_append(v___x_4729_, v___x_4730_);
    if lean_obj_tag(v_parentDecl_x3f_4725_) == 1 {
        let mut v_val_4732_: *mut LeanObject = core::ptr::null_mut();
        let mut v_env_4733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: u8 = 0;
        v_val_4732_ = lean_ctor_get(v_parentDecl_x3f_4725_, 0);
        lean_inc_n(v_val_4732_, 2);
        lean_dec_ref_known(v_parentDecl_x3f_4725_, 1);
        v_env_4733_ = lean_ctor_get(v_toCommandContextInfo_4724_, 0);
        lean_inc_ref_n(v_env_4733_, 2);
        lean_dec_ref(v_toCommandContextInfo_4724_);
        v___x_4734_ = l_Lean_isMarkedMeta(v_env_4733_, v_val_4732_);
        if v___x_4734_ == 0 {
            let mut v_isExporting_4735_: u8 = 0;
            lean_dec(v_val_4732_);
            v_isExporting_4735_ = lean_ctor_get_uint8(
                v_env_4733_,
                (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
            );
            lean_dec_ref(v_env_4733_);
            if v_isExporting_4735_ == 0 {
                return v_text_4731_;
            } else {
                let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
                let mut v_text_4737_: *mut LeanObject = core::ptr::null_mut();
                v___x_4736_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                v_text_4737_ = lean_string_append(v___x_4736_, v_text_4731_);
                lean_dec_ref(v_text_4731_);
                return v_text_4737_;
            }
        } else {
            let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
            let mut v_text_4739_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4740_: u8 = 0;
            lean_dec_ref(v_env_4733_);
            v___x_4738_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3;
            v_text_4739_ = lean_string_append(v___x_4738_, v_text_4731_);
            lean_dec_ref(v_text_4731_);
            v___x_4740_ = l_Lean_isPrivateName(v_val_4732_);
            lean_dec(v_val_4732_);
            if v___x_4740_ == 0 {
                if v___x_4734_ == 0 {
                    return v_text_4739_;
                } else {
                    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_text_4742_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4741_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2;
                    v_text_4742_ = lean_string_append(v___x_4741_, v_text_4739_);
                    lean_dec_ref(v_text_4739_);
                    return v_text_4742_;
                }
            } else {
                return v_text_4739_;
            }
        }
    } else {
        lean_dec(v_parentDecl_x3f_4725_);
        lean_dec_ref(v_toCommandContextInfo_4724_);
        return v_text_4731_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(
    mut v_x_4744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_response_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_code_4764_: u8 = 0;
    let mut v_message_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4744_) == 0 {
                    v_response_4745_ = lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4763_ = (!lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4747_ = v_x_4744_;
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_response_4745_);
                        lean_dec(v_x_4744_);
                        v___x_4747_ = lean_box(0);
                        v_isShared_4748_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_code_4764_ = lean_ctor_get_uint8(
                        v_x_4744_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_message_4765_ = lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4772_ = (!lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4772_ == 0 {
                        v___x_4767_ = v_x_4744_;
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_message_4765_);
                        lean_dec(v_x_4744_);
                        v___x_4767_ = lean_box(0);
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_response_4745_);
                v___x_4749_ =
                    l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_4745_);
                if lean_obj_tag(v___x_4749_) == 0 {
                    lean_del_object(v___x_4747_);
                    v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
                    lean_inc(v_a_4750_);
                    lean_dec_ref_known(v___x_4749_, 1);
                    v___x_4751_ = 0;
                    v___x_4752_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0;
                    v___x_4753_ = l_Lean_Json_compress(v_response_4745_);
                    v___x_4754_ = lean_string_append(v___x_4752_, v___x_4753_);
                    lean_dec_ref(v___x_4753_);
                    v___x_4755_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1;
                    v___x_4756_ = lean_string_append(v___x_4754_, v___x_4755_);
                    v___x_4757_ = lean_string_append(v___x_4756_, v_a_4750_);
                    lean_dec(v_a_4750_);
                    v___x_4758_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v___x_4758_, 0, v___x_4757_);
                    lean_ctor_set_uint8(
                        v___x_4758_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4751_,
                    );
                    return v___x_4758_;
                } else {
                    lean_dec(v_response_4745_);
                    v_a_4759_ = lean_ctor_get(v___x_4749_, 0);
                    lean_inc(v_a_4759_);
                    lean_dec_ref_known(v___x_4749_, 1);
                    if v_isShared_4748_ == 0 {
                        lean_ctor_set(v___x_4747_, 0, v_a_4759_);
                        v___x_4761_ = v___x_4747_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4759_);
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
                    v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_message_4765_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_method_4774_: *mut LeanObject,
    mut v_param_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_serverRequestEmitter_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    v_serverRequestEmitter_4778_ = lean_ctor_get(v_a_4776_, 5);
    v___x_4779_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_4775_);
    lean_inc_ref(v_serverRequestEmitter_4778_);
    v___x_4780_ = lean_apply_3(
        v_serverRequestEmitter_4778_,
        v_method_4774_,
        v___x_4779_,
        lean_box(0),
    );
    v___f_4781_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0;
    v___x_4782_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4781_, v___x_4780_);
    v___x_4783_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4783_, 0, v___x_4782_);
    return v___x_4783_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(
    mut v_method_4784_: *mut LeanObject,
    mut v_param_4785_: *mut LeanObject,
    mut v_a_4786_: *mut LeanObject,
    mut v_a_4787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4788_: *mut LeanObject = core::ptr::null_mut();
    v_res_4788_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_4784_, v_param_4785_, v_a_4786_);
    lean_dec_ref(v_a_4786_);
    return v_res_4788_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(
    mut v_val_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    v___x_4790_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4790_, 0, v_val_4789_);
    return v___x_4790_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(
    mut v_val_4791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    v___x_4792_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4792_, 0, v_val_4791_);
    return v___x_4792_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(
    mut v_sz_4793_: usize,
    mut v_i_4794_: usize,
    mut v_bs_4795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4796_: u8 = 0;
    let mut v_v_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanModuleQuery_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: usize = 0;
    let mut v___x_4802_: usize = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
                if v___x_4796_ == 0 {
                    return v_bs_4795_;
                } else {
                    v_v_4797_ = lean_array_uget_borrowed(v_bs_4795_, v_i_4794_);
                    v_toLeanModuleQuery_4798_ = lean_ctor_get(v_v_4797_, 0);
                    lean_inc_ref(v_toLeanModuleQuery_4798_);
                    v___x_4799_ = lean_unsigned_to_nat(0);
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
    mut v_sz_4805_: *mut LeanObject,
    mut v_i_4806_: *mut LeanObject,
    mut v_bs_4807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4808_: usize = 0;
    let mut v_i_boxed_4809_: usize = 0;
    let mut v_res_4810_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4808_ = lean_unbox_usize(v_sz_4805_);
    lean_dec(v_sz_4805_);
    v_i_boxed_4809_ = lean_unbox_usize(v_i_4806_);
    lean_dec(v_i_4806_);
    v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_4808_, v_i_boxed_4809_, v_bs_4807_);
    return v_res_4810_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(
    mut v_a_4814_: *mut LeanObject,
    mut v_kind_4815_: *mut LeanObject,
    mut v___x_4816_: *mut LeanObject,
    mut v_params_4817_: *mut LeanObject,
    mut v___x_4818_: *mut LeanObject,
    mut v___x_4819_: *mut LeanObject,
    mut v_as_4820_: *mut LeanObject,
    mut v_sz_4821_: usize,
    mut v_i_4822_: usize,
    mut v_b_4823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_4835_: u8 = 0;
    let mut v_fst_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v_ctx_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4844_: u8 = 0;
    let mut v___y_4845_: u8 = 0;
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fullName_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_edit_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut v_fullName_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_edit_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u8 = 0;
    let mut v___y_4924_: u8 = 0;
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v___x_4927_: u8 = 0;
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4830_ = lean_usize_dec_lt(v_i_4822_, v_sz_4821_);
                if v___x_4830_ == 0 {
                    lean_dec_ref(v___x_4818_);
                    lean_dec_ref(v_params_4817_);
                    lean_dec_ref(v___x_4816_);
                    lean_dec_ref(v_kind_4815_);
                    lean_dec_ref(v_a_4814_);
                    v___x_4831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4831_, 0, v_b_4823_);
                    return v___x_4831_;
                } else {
                    v_a_4832_ = lean_array_uget_borrowed(v_as_4820_, v_i_4822_);
                    v_module_4833_ = lean_ctor_get(v_a_4832_, 0);
                    v_decl_4834_ = lean_ctor_get(v_a_4832_, 1);
                    v_isExactMatch_4835_ = lean_ctor_get_uint8(
                        v_a_4832_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_fst_4836_ = lean_ctor_get(v_b_4823_, 0);
                    v_snd_4837_ = lean_ctor_get(v_b_4823_, 1);
                    v_isSharedCheck_4928_ = (!lean_is_exclusive(v_b_4823_)) as u8;
                    if v_isSharedCheck_4928_ == 0 {
                        v___x_4839_ = v_b_4823_;
                        v_isShared_4840_ = v_isSharedCheck_4928_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4837_);
                        lean_inc(v_fst_4836_);
                        lean_dec(v_b_4823_);
                        v___x_4839_ = lean_box(0);
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
                v_ctx_4841_ = lean_ctor_get(v_a_4814_, 1);
                v_determineInsertion_4842_ = lean_ctor_get(v_a_4814_, 2);
                v_toCommandContextInfo_4919_ = lean_ctor_get(v_ctx_4841_, 0);
                v_env_4920_ = lean_ctor_get(v_toCommandContextInfo_4919_, 0);
                v___x_4921_ = lean_unsigned_to_nat(0);
                v___x_4922_ = lean_nat_dec_eq(v___x_4819_, v___x_4921_);
                lean_inc(v_decl_4834_);
                lean_inc_ref(v_env_4920_);
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
                    lean_inc_ref(v_determineInsertion_4842_);
                    lean_inc(v_decl_4834_);
                    v___x_4846_ = lean_apply_1(v_determineInsertion_4842_, v_decl_4834_);
                    if v___y_4844_ == 0 {
                        v_fullName_4847_ = lean_ctor_get(v___x_4846_, 0);
                        v_edit_4848_ = lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4875_ = (!lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4875_ == 0 {
                            v___x_4850_ = v___x_4846_;
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_edit_4848_);
                            lean_inc(v_fullName_4847_);
                            lean_dec(v___x_4846_);
                            v___x_4850_ = lean_box(0);
                            v_isShared_4851_ = v_isSharedCheck_4875_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_fullName_4876_ = lean_ctor_get(v___x_4846_, 0);
                        v_edit_4877_ = lean_ctor_get(v___x_4846_, 1);
                        v_isSharedCheck_4915_ = (!lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4915_ == 0 {
                            v___x_4879_ = v___x_4846_;
                            v_isShared_4880_ = v_isSharedCheck_4915_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_edit_4877_);
                            lean_inc(v_fullName_4876_);
                            lean_dec(v___x_4846_);
                            v___x_4879_ = lean_box(0);
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
                        v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_fst_4836_);
                        lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_snd_4837_);
                        v___x_4917_ = v_reuseFailAlloc_4918_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4852_ = lean_box(0);
                v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
                v___x_4854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4847_,
                    v___x_4830_,
                );
                v___x_4855_ = lean_string_append(v___x_4853_, v___x_4854_);
                lean_dec_ref(v___x_4854_);
                lean_inc_ref(v_kind_4815_);
                v___x_4856_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4856_, 0, v_kind_4815_);
                lean_inc_ref(v___x_4816_);
                v___x_4857_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                v___x_4858_ = lean_unsigned_to_nat(1);
                v___x_4859_ = lean_mk_empty_array_with_capacity(v___x_4858_);
                v___x_4860_ = lean_array_push(v___x_4859_, v_edit_4848_);
                if v_isShared_4851_ == 0 {
                    lean_ctor_set(v___x_4850_, 1, v___x_4860_);
                    lean_ctor_set(v___x_4850_, 0, v___x_4857_);
                    v___x_4862_ = v___x_4850_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4857_);
                    lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4860_);
                    v___x_4862_ = v_reuseFailAlloc_4874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4863_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4862_);
                v___x_4864_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4864_, 0, v___x_4863_);
                v___x_4865_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                lean_inc_ref(v_params_4817_);
                v___x_4866_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4865_,
                );
                v___x_4867_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4866_);
                v___x_4868_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4868_, 0, v___x_4867_);
                v___x_4869_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_4869_, 0, v___x_4852_);
                lean_ctor_set(v___x_4869_, 1, v___x_4852_);
                lean_ctor_set(v___x_4869_, 2, v___x_4855_);
                lean_ctor_set(v___x_4869_, 3, v___x_4856_);
                lean_ctor_set(v___x_4869_, 4, v___x_4852_);
                lean_ctor_set(v___x_4869_, 5, v___x_4852_);
                lean_ctor_set(v___x_4869_, 6, v___x_4852_);
                lean_ctor_set(v___x_4869_, 7, v___x_4864_);
                lean_ctor_set(v___x_4869_, 8, v___x_4852_);
                lean_ctor_set(v___x_4869_, 9, v___x_4868_);
                v___x_4870_ = lean_array_push(v_fst_4836_, v___x_4869_);
                if v_isShared_4840_ == 0 {
                    lean_ctor_set(v___x_4839_, 0, v___x_4870_);
                    v___x_4872_ = v___x_4839_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
                    lean_ctor_set(v_reuseFailAlloc_4873_, 1, v_snd_4837_);
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
                v___x_4881_ = lean_box(0);
                v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
                v___x_4883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fullName_4876_,
                    v___y_4844_,
                );
                v___x_4884_ = lean_string_append(v___x_4882_, v___x_4883_);
                lean_dec_ref(v___x_4883_);
                v___x_4885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
                v___x_4886_ = lean_string_append(v___x_4884_, v___x_4885_);
                lean_inc_n(v_module_4833_, 2);
                v___x_4887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_module_4833_,
                    v___y_4844_,
                );
                v___x_4888_ = lean_string_append(v___x_4886_, v___x_4887_);
                lean_dec_ref(v___x_4887_);
                lean_inc_ref(v_kind_4815_);
                v___x_4889_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4889_, 0, v_kind_4815_);
                lean_inc_ref(v___x_4816_);
                v___x_4890_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_4816_);
                lean_inc_ref(v_ctx_4841_);
                v___x_4891_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_4841_, v_module_4833_);
                lean_inc_ref(v___x_4818_);
                v___x_4892_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4892_, 0, v___x_4818_);
                lean_ctor_set(v___x_4892_, 1, v___x_4891_);
                lean_ctor_set(v___x_4892_, 2, v___x_4881_);
                lean_ctor_set(v___x_4892_, 3, v___x_4881_);
                v___x_4893_ = lean_unsigned_to_nat(2);
                v___x_4894_ = lean_mk_empty_array_with_capacity(v___x_4893_);
                v___x_4895_ = lean_array_push(v___x_4894_, v___x_4892_);
                v___x_4896_ = lean_array_push(v___x_4895_, v_edit_4877_);
                if v_isShared_4880_ == 0 {
                    lean_ctor_set(v___x_4879_, 1, v___x_4896_);
                    lean_ctor_set(v___x_4879_, 0, v___x_4890_);
                    v___x_4898_ = v___x_4879_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4890_);
                    lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4896_);
                    v___x_4898_ = v_reuseFailAlloc_4914_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4899_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_4898_);
                v___x_4900_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4900_, 0, v___x_4899_);
                v___x_4901_ = l_Lean_Server_FileWorker_importUnknownIdentifiersProvider;
                lean_inc_ref(v_params_4817_);
                v___x_4902_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(
                    v_params_4817_,
                    v___x_4901_,
                );
                v___x_4903_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4902_);
                v___x_4904_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4904_, 0, v___x_4903_);
                v___x_4905_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_4905_, 0, v___x_4881_);
                lean_ctor_set(v___x_4905_, 1, v___x_4881_);
                lean_ctor_set(v___x_4905_, 2, v___x_4888_);
                lean_ctor_set(v___x_4905_, 3, v___x_4889_);
                lean_ctor_set(v___x_4905_, 4, v___x_4881_);
                lean_ctor_set(v___x_4905_, 5, v___x_4881_);
                lean_ctor_set(v___x_4905_, 6, v___x_4881_);
                lean_ctor_set(v___x_4905_, 7, v___x_4900_);
                lean_ctor_set(v___x_4905_, 8, v___x_4881_);
                lean_ctor_set(v___x_4905_, 9, v___x_4904_);
                v___x_4906_ = lean_array_push(v_fst_4836_, v___x_4905_);
                if v_isExactMatch_4835_ == 0 {
                    if v_isShared_4840_ == 0 {
                        lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4908_ = v___x_4839_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4906_);
                        lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_snd_4837_);
                        v___x_4908_ = v_reuseFailAlloc_4909_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4837_);
                    v___x_4910_ = lean_box((v___x_4830_) as usize);
                    if v_isShared_4840_ == 0 {
                        lean_ctor_set(v___x_4839_, 1, v___x_4910_);
                        lean_ctor_set(v___x_4839_, 0, v___x_4906_);
                        v___x_4912_ = v___x_4839_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4906_);
                        lean_ctor_set(v_reuseFailAlloc_4913_, 1, v___x_4910_);
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
                    lean_dec(v___x_4925_);
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
    mut v_a_4929_: *mut LeanObject,
    mut v_kind_4930_: *mut LeanObject,
    mut v___x_4931_: *mut LeanObject,
    mut v_params_4932_: *mut LeanObject,
    mut v___x_4933_: *mut LeanObject,
    mut v___x_4934_: *mut LeanObject,
    mut v_as_4935_: *mut LeanObject,
    mut v_sz_4936_: *mut LeanObject,
    mut v_i_4937_: *mut LeanObject,
    mut v_b_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4940_: usize = 0;
    let mut v_i_boxed_4941_: usize = 0;
    let mut v_res_4942_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4940_ = lean_unbox_usize(v_sz_4936_);
    lean_dec(v_sz_4936_);
    v_i_boxed_4941_ = lean_unbox_usize(v_i_4937_);
    lean_dec(v_i_4937_);
    v_res_4942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4929_, v_kind_4930_, v___x_4931_, v_params_4932_, v___x_4933_, v___x_4934_, v_as_4935_, v_sz_boxed_4940_, v_i_boxed_4941_, v_b_4938_);
    lean_dec_ref(v_as_4935_);
    lean_dec(v___x_4934_);
    return v_res_4942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(
    mut v_kind_4943_: *mut LeanObject,
    mut v___x_4944_: *mut LeanObject,
    mut v_params_4945_: *mut LeanObject,
    mut v___x_4946_: *mut LeanObject,
    mut v___x_4947_: *mut LeanObject,
    mut v_as_4948_: *mut LeanObject,
    mut v_sz_4949_: usize,
    mut v_i_4950_: usize,
    mut v_b_4951_: *mut LeanObject,
    mut v___y_4952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v_fst_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v_array_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: u8 = 0;
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_a_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4984_: usize = 0;
    let mut v___x_4985_: usize = 0;
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v_reuseFailAlloc_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_reuseFailAlloc_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut v_unused_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v_unused_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4954_ = lean_usize_dec_lt(v_i_4950_, v_sz_4949_);
                if v___x_4954_ == 0 {
                    lean_dec_ref(v___x_4946_);
                    lean_dec_ref(v_params_4945_);
                    lean_dec_ref(v___x_4944_);
                    lean_dec_ref(v_kind_4943_);
                    v___x_4955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4955_, 0, v_b_4951_);
                    return v___x_4955_;
                } else {
                    v_snd_4956_ = lean_ctor_get(v_b_4951_, 1);
                    lean_inc(v_snd_4956_);
                    v_snd_4957_ = lean_ctor_get(v_snd_4956_, 1);
                    lean_inc(v_snd_4957_);
                    v_fst_4958_ = lean_ctor_get(v_b_4951_, 0);
                    v_isSharedCheck_5023_ = (!lean_is_exclusive(v_b_4951_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v_unused_5024_ = lean_ctor_get(v_b_4951_, 1);
                        lean_dec(v_unused_5024_);
                        v___x_4960_ = v_b_4951_;
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_4958_);
                        lean_dec(v_b_4951_);
                        v___x_4960_ = lean_box(0);
                        v_isShared_4961_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4962_ = lean_ctor_get(v_snd_4956_, 0);
                v_isSharedCheck_5021_ = (!lean_is_exclusive(v_snd_4956_)) as u8;
                if v_isSharedCheck_5021_ == 0 {
                    v_unused_5022_ = lean_ctor_get(v_snd_4956_, 1);
                    lean_dec(v_unused_5022_);
                    v___x_4964_ = v_snd_4956_;
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_4962_);
                    lean_dec(v_snd_4956_);
                    v___x_4964_ = lean_box(0);
                    v_isShared_4965_ = v_isSharedCheck_5021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_array_4966_ = lean_ctor_get(v_snd_4957_, 0);
                v_start_4967_ = lean_ctor_get(v_snd_4957_, 1);
                v_stop_4968_ = lean_ctor_get(v_snd_4957_, 2);
                v___x_4969_ = lean_nat_dec_lt(v_start_4967_, v_stop_4968_);
                if v___x_4969_ == 0 {
                    lean_dec_ref(v___x_4946_);
                    lean_dec_ref(v_params_4945_);
                    lean_dec_ref(v___x_4944_);
                    lean_dec_ref(v_kind_4943_);
                    if v_isShared_4965_ == 0 {
                        v___x_4971_ = v___x_4964_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_fst_4962_);
                        lean_ctor_set(v_reuseFailAlloc_4976_, 1, v_snd_4957_);
                        v___x_4971_ = v_reuseFailAlloc_4976_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_4968_);
                    lean_inc(v_start_4967_);
                    lean_inc_ref(v_array_4966_);
                    v_isSharedCheck_5017_ = (!lean_is_exclusive(v_snd_4957_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = lean_ctor_get(v_snd_4957_, 2);
                        lean_dec(v_unused_5018_);
                        v_unused_5019_ = lean_ctor_get(v_snd_4957_, 1);
                        lean_dec(v_unused_5019_);
                        v_unused_5020_ = lean_ctor_get(v_snd_4957_, 0);
                        lean_dec(v_unused_5020_);
                        v___x_4978_ = v_snd_4957_;
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_snd_4957_);
                        v___x_4978_ = lean_box(0);
                        v_isShared_4979_ = v_isSharedCheck_5017_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4961_ == 0 {
                    lean_ctor_set(v___x_4960_, 1, v___x_4971_);
                    v___x_4973_ = v___x_4960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_fst_4958_);
                    lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4971_);
                    v___x_4973_ = v_reuseFailAlloc_4975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4974_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4974_, 0, v___x_4973_);
                return v___x_4974_;
            }
            5 => {
                v_a_4980_ = lean_array_uget_borrowed(v_as_4948_, v_i_4950_);
                v___x_4981_ = lean_array_fget_borrowed(v_array_4966_, v_start_4967_);
                if v_isShared_4965_ == 0 {
                    lean_ctor_set(v___x_4964_, 1, v_fst_4962_);
                    lean_ctor_set(v___x_4964_, 0, v_fst_4958_);
                    v___x_4983_ = v___x_4964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_fst_4958_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_fst_4962_);
                    v___x_4983_ = v_reuseFailAlloc_5016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_sz_4984_ = lean_array_size(v___x_4981_);
                v___x_4985_ = 0usize;
                lean_inc_ref(v___x_4946_);
                lean_inc_ref(v_params_4945_);
                lean_inc_ref(v___x_4944_);
                lean_inc_ref(v_kind_4943_);
                lean_inc(v_a_4980_);
                v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_4980_, v_kind_4943_, v___x_4944_, v_params_4945_, v___x_4946_, v___x_4947_, v___x_4981_, v_sz_4984_, v___x_4985_, v___x_4983_);
                if lean_obj_tag(v___x_4986_) == 0 {
                    v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
                    lean_inc(v_a_4987_);
                    lean_dec_ref_known(v___x_4986_, 1);
                    v_fst_4988_ = lean_ctor_get(v_a_4987_, 0);
                    v_snd_4989_ = lean_ctor_get(v_a_4987_, 1);
                    v_isSharedCheck_5007_ = (!lean_is_exclusive(v_a_4987_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_4991_ = v_a_4987_;
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_4989_);
                        lean_inc(v_fst_4988_);
                        lean_dec(v_a_4987_);
                        v___x_4991_ = lean_box(0);
                        v_isShared_4992_ = v_isSharedCheck_5007_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4978_);
                    lean_dec(v_stop_4968_);
                    lean_dec(v_start_4967_);
                    lean_dec_ref(v_array_4966_);
                    lean_del_object(v___x_4960_);
                    lean_dec_ref(v___x_4946_);
                    lean_dec_ref(v_params_4945_);
                    lean_dec_ref(v___x_4944_);
                    lean_dec_ref(v_kind_4943_);
                    v_a_5008_ = lean_ctor_get(v___x_4986_, 0);
                    v_isSharedCheck_5015_ = (!lean_is_exclusive(v___x_4986_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5010_ = v___x_4986_;
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5008_);
                        lean_dec(v___x_4986_);
                        v___x_5010_ = lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4993_ = lean_unsigned_to_nat(1);
                v___x_4994_ = lean_nat_add(v_start_4967_, v___x_4993_);
                lean_dec(v_start_4967_);
                if v_isShared_4979_ == 0 {
                    lean_ctor_set(v___x_4978_, 1, v___x_4994_);
                    v___x_4996_ = v___x_4978_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_array_4966_);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 1, v___x_4994_);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 2, v_stop_4968_);
                    v___x_4996_ = v_reuseFailAlloc_5006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4992_ == 0 {
                    lean_ctor_set(v___x_4991_, 1, v___x_4996_);
                    lean_ctor_set(v___x_4991_, 0, v_snd_4989_);
                    v___x_4998_ = v___x_4991_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_snd_4989_);
                    lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_5005_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4961_ == 0 {
                    lean_ctor_set(v___x_4960_, 1, v___x_4998_);
                    lean_ctor_set(v___x_4960_, 0, v_fst_4988_);
                    v___x_5000_ = v___x_4960_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_fst_4988_);
                    lean_ctor_set(v_reuseFailAlloc_5004_, 1, v___x_4998_);
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
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
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
    mut v_kind_5025_: *mut LeanObject,
    mut v___x_5026_: *mut LeanObject,
    mut v_params_5027_: *mut LeanObject,
    mut v___x_5028_: *mut LeanObject,
    mut v___x_5029_: *mut LeanObject,
    mut v_as_5030_: *mut LeanObject,
    mut v_sz_5031_: *mut LeanObject,
    mut v_i_5032_: *mut LeanObject,
    mut v_b_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5036_: usize = 0;
    let mut v_i_boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5036_ = lean_unbox_usize(v_sz_5031_);
    lean_dec(v_sz_5031_);
    v_i_boxed_5037_ = lean_unbox_usize(v_i_5032_);
    lean_dec(v_i_5032_);
    v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5025_, v___x_5026_, v_params_5027_, v___x_5028_, v___x_5029_, v_as_5030_, v_sz_boxed_5036_, v_i_boxed_5037_, v_b_5033_, v___y_5034_);
    lean_dec_ref(v___y_5034_);
    lean_dec_ref(v_as_5030_);
    lean_dec(v___x_5029_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
    mut v_id_5047_: *mut LeanObject,
    mut v_params_5048_: *mut LeanObject,
    mut v_requestedRange_5049_: *mut LeanObject,
    mut v_kind_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_doc_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5059_: u8 = 0;
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___f_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_unused_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_val_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_response_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v_snd_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v_fst_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_initSnap_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5162_: u8 = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_unused_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut v_reuseFailAlloc_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_unused_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5053_ = lean_ctor_get(v_a_5051_, 1);
                v_cancelTk_5054_ = lean_ctor_get(v_a_5051_, 4);
                v_toEditableDocumentCore_5055_ = lean_ctor_get(v_doc_5053_, 0);
                v_stop_5056_ = lean_ctor_get(v_requestedRange_5049_, 1);
                v_isSharedCheck_5185_ = (!lean_is_exclusive(v_requestedRange_5049_)) as u8;
                if v_isSharedCheck_5185_ == 0 {
                    v_unused_5186_ = lean_ctor_get(v_requestedRange_5049_, 0);
                    lean_dec(v_unused_5186_);
                    v___x_5058_ = v_requestedRange_5049_;
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_5056_);
                    lean_dec(v_requestedRange_5049_);
                    v___x_5058_ = lean_box(0);
                    v_isShared_5059_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_doc_5053_);
                v___x_5060_ =
                    l_Lean_Server_FileWorker_computeQueries(v_doc_5053_, v_stop_5056_, v_a_5051_);
                if lean_obj_tag(v___x_5060_) == 0 {
                    v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5176_ = (!lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5063_ = v___x_5060_;
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5061_);
                        lean_dec(v___x_5060_);
                        v___x_5063_ = lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5176_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5058_);
                    lean_dec_ref(v_kind_5050_);
                    lean_dec_ref(v_params_5048_);
                    lean_dec(v_id_5047_);
                    v_a_5177_ = lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5184_ = (!lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5184_ == 0 {
                        v___x_5179_ = v___x_5060_;
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_5177_);
                        lean_dec(v___x_5060_);
                        v___x_5179_ = lean_box(0);
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5065_ = lean_array_get_size(v_a_5061_);
                v___x_5066_ = lean_unsigned_to_nat(0);
                v___x_5067_ = lean_nat_dec_eq(v___x_5065_, v___x_5066_);
                if v___x_5067_ == 0 {
                    lean_del_object(v___x_5063_);
                    v___x_5068_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5069_ = lean_array_size(v_a_5061_);
                    v___x_5070_ = 0usize;
                    lean_inc(v_a_5061_);
                    v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5069_, v___x_5070_, v_a_5061_);
                    if v_isShared_5059_ == 0 {
                        lean_ctor_set(v___x_5058_, 1, v___x_5071_);
                        lean_ctor_set(v___x_5058_, 0, v_id_5047_);
                        v___x_5073_ = v___x_5058_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_id_5047_);
                        lean_ctor_set(v_reuseFailAlloc_5171_, 1, v___x_5071_);
                        v___x_5073_ = v_reuseFailAlloc_5171_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5061_);
                    lean_del_object(v___x_5058_);
                    lean_dec_ref(v_kind_5050_);
                    lean_dec_ref(v_params_5048_);
                    lean_dec(v_id_5047_);
                    v___x_5172_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                    if v_isShared_5064_ == 0 {
                        lean_ctor_set(v___x_5063_, 0, v___x_5172_);
                        v___x_5174_ = v___x_5063_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
                        v___x_5174_ = v_reuseFailAlloc_5175_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5074_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5068_, v___x_5073_, v_a_5051_);
                v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
                v_isSharedCheck_5170_ = (!lean_is_exclusive(v___x_5074_)) as u8;
                if v_isSharedCheck_5170_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    v_isShared_5078_ = v_isSharedCheck_5170_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_5075_);
                    lean_dec(v___x_5074_);
                    v___x_5077_ = lean_box(0);
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
                v___x_5084_ = lean_box(0);
                v___x_5085_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5085_, 0, v___x_5083_);
                lean_ctor_set(v___x_5085_, 1, v___x_5084_);
                v___x_5086_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5086_, 0, v___x_5081_);
                lean_ctor_set(v___x_5086_, 1, v___x_5085_);
                v___x_5087_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_5086_);
                if lean_obj_tag(v___x_5087_) == 0 {
                    v_val_5108_ = lean_ctor_get(v___x_5087_, 0);
                    lean_inc(v_val_5108_);
                    lean_dec_ref_known(v___x_5087_, 1);
                    if lean_obj_tag(v_val_5108_) == 0 {
                        v_response_5109_ = lean_ctor_get(v_val_5108_, 0);
                        lean_inc(v_response_5109_);
                        lean_dec_ref_known(v_val_5108_, 1);
                        v_initSnap_5151_ = lean_ctor_get(v_toEditableDocumentCore_5055_, 1);
                        v_meta_5152_ = lean_ctor_get(v_toEditableDocumentCore_5055_, 0);
                        v_stx_5153_ = lean_ctor_get(v_initSnap_5151_, 3);
                        v___x_5154_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5153_, v___x_5067_);
                        if lean_obj_tag(v___x_5154_) == 0 {
                            v___x_5155_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5;
                            v___y_5111_ = v___x_5155_;
                            state = 10;
                            continue;
                        } else {
                            v_val_5156_ = lean_ctor_get(v___x_5154_, 0);
                            lean_inc(v_val_5156_);
                            lean_dec_ref_known(v___x_5154_, 1);
                            v_text_5157_ = lean_ctor_get(v_meta_5152_, 3);
                            lean_inc_ref(v_text_5157_);
                            v___x_5158_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5157_, v_val_5156_);
                            lean_dec(v_val_5156_);
                            v_line_5159_ = lean_ctor_get(v___x_5158_, 0);
                            v_isSharedCheck_5168_ = (!lean_is_exclusive(v___x_5158_)) as u8;
                            if v_isSharedCheck_5168_ == 0 {
                                v_unused_5169_ = lean_ctor_get(v___x_5158_, 1);
                                lean_dec(v_unused_5169_);
                                v___x_5161_ = v___x_5158_;
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_line_5159_);
                                lean_dec(v___x_5158_);
                                v___x_5161_ = lean_box(0);
                                v_isShared_5162_ = v_isSharedCheck_5168_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_5108_);
                        lean_del_object(v___x_5077_);
                        lean_dec(v_a_5061_);
                        lean_dec_ref(v_kind_5050_);
                        lean_dec_ref(v_params_5048_);
                        v___y_5089_ = v_a_5051_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5087_);
                    lean_del_object(v___x_5077_);
                    lean_dec(v_a_5061_);
                    lean_dec_ref(v_kind_5050_);
                    lean_dec_ref(v_params_5048_);
                    v___y_5089_ = v_a_5051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5090_ = l_Lean_Server_RequestM_checkCancelled(v___y_5089_);
                if lean_obj_tag(v___x_5090_) == 0 {
                    v_isSharedCheck_5098_ = (!lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5098_ == 0 {
                        v_unused_5099_ = lean_ctor_get(v___x_5090_, 0);
                        lean_dec(v_unused_5099_);
                        v___x_5092_ = v___x_5090_;
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_5090_);
                        v___x_5092_ = lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5098_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_5100_ = lean_ctor_get(v___x_5090_, 0);
                    v_isSharedCheck_5107_ = (!lean_is_exclusive(v___x_5090_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5102_ = v___x_5090_;
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5100_);
                        lean_dec(v___x_5090_);
                        v___x_5102_ = lean_box(0);
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
                    lean_ctor_set(v___x_5092_, 0, v___x_5094_);
                    v___x_5096_ = v___x_5092_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
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
                    v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5105_;
            }
            10 => {
                lean_inc_ref(v___y_5111_);
                v___x_5112_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5112_, 0, v___y_5111_);
                lean_ctor_set(v___x_5112_, 1, v___y_5111_);
                v___x_5113_ =
                    l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3;
                v___x_5114_ = lean_array_get_size(v_response_5109_);
                v___x_5115_ = lean_nat_dec_lt(v___x_5066_, v___x_5114_);
                if v___x_5115_ == 0 {
                    lean_dec_ref_known(v___x_5112_, 2);
                    lean_dec(v_response_5109_);
                    lean_dec(v_a_5061_);
                    lean_dec_ref(v_kind_5050_);
                    lean_dec_ref(v_params_5048_);
                    if v_isShared_5078_ == 0 {
                        lean_ctor_set(v___x_5077_, 0, v___x_5113_);
                        v___x_5117_ = v___x_5077_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5113_);
                        v___x_5117_ = v_reuseFailAlloc_5118_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5077_);
                    v___x_5119_ =
                        l_Array_toSubarray___redArg(v_response_5109_, v___x_5066_, v___x_5114_);
                    v___x_5120_ = lean_box((v___x_5067_) as usize);
                    v___x_5121_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5121_, 0, v___x_5120_);
                    lean_ctor_set(v___x_5121_, 1, v___x_5119_);
                    v___x_5122_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5122_, 0, v___x_5113_);
                    lean_ctor_set(v___x_5122_, 1, v___x_5121_);
                    lean_inc_ref(v_params_5048_);
                    lean_inc_ref(v_doc_5053_);
                    v___x_5123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_5050_, v_doc_5053_, v_params_5048_, v___x_5112_, v___x_5065_, v_a_5061_, v_sz_5069_, v___x_5070_, v___x_5122_, v_a_5051_);
                    lean_dec(v_a_5061_);
                    if lean_obj_tag(v___x_5123_) == 0 {
                        v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5142_ = (!lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v___x_5126_ = v___x_5123_;
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5124_);
                            lean_dec(v___x_5123_);
                            v___x_5126_ = lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5142_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_params_5048_);
                        v_a_5143_ = lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5150_ = (!lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5123_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5143_);
                            lean_dec(v___x_5123_);
                            v___x_5145_ = lean_box(0);
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
                v_snd_5128_ = lean_ctor_get(v_a_5124_, 1);
                v_fst_5129_ = lean_ctor_get(v_snd_5128_, 0);
                v___x_5130_ = (lean_unbox(v_fst_5129_) as u8);
                if v___x_5130_ == 0 {
                    lean_dec_ref(v_params_5048_);
                    v_fst_5131_ = lean_ctor_get(v_a_5124_, 0);
                    lean_inc(v_fst_5131_);
                    lean_dec(v_a_5124_);
                    if v_isShared_5127_ == 0 {
                        lean_ctor_set(v___x_5126_, 0, v_fst_5131_);
                        v___x_5133_ = v___x_5126_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_fst_5131_);
                        v___x_5133_ = v_reuseFailAlloc_5134_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_fst_5135_ = lean_ctor_get(v_a_5124_, 0);
                    lean_inc(v_fst_5135_);
                    lean_dec(v_a_5124_);
                    v___x_5136_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4;
                    v___x_5137_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(
                        v_params_5048_,
                        v___x_5136_,
                    );
                    v___x_5138_ = lean_array_push(v_fst_5135_, v___x_5137_);
                    if v_isShared_5127_ == 0 {
                        lean_ctor_set(v___x_5126_, 0, v___x_5138_);
                        v___x_5140_ = v___x_5126_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
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
                    v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5148_;
            }
            17 => {
                v___x_5163_ = lean_unsigned_to_nat(1);
                v___x_5164_ = lean_nat_add(v_line_5159_, v___x_5163_);
                lean_dec(v_line_5159_);
                if v_isShared_5162_ == 0 {
                    lean_ctor_set(v___x_5161_, 1, v___x_5066_);
                    lean_ctor_set(v___x_5161_, 0, v___x_5164_);
                    v___x_5166_ = v___x_5161_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
                    lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5066_);
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
                    v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
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
    mut v_id_5187_: *mut LeanObject,
    mut v_params_5188_: *mut LeanObject,
    mut v_requestedRange_5189_: *mut LeanObject,
    mut v_kind_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
    mut v_a_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5193_: *mut LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(
        v_id_5187_,
        v_params_5188_,
        v_requestedRange_5189_,
        v_kind_5190_,
        v_a_5191_,
    );
    lean_dec_ref(v_a_5191_);
    return v_res_5193_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(
    mut v_a_5194_: *mut LeanObject,
    mut v_kind_5195_: *mut LeanObject,
    mut v___x_5196_: *mut LeanObject,
    mut v_params_5197_: *mut LeanObject,
    mut v___x_5198_: *mut LeanObject,
    mut v___x_5199_: *mut LeanObject,
    mut v_as_5200_: *mut LeanObject,
    mut v_sz_5201_: usize,
    mut v_i_5202_: usize,
    mut v_b_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_5194_, v_kind_5195_, v___x_5196_, v_params_5197_, v___x_5198_, v___x_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_);
    return v___x_5206_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(
    mut v_a_5207_: *mut LeanObject,
    mut v_kind_5208_: *mut LeanObject,
    mut v___x_5209_: *mut LeanObject,
    mut v_params_5210_: *mut LeanObject,
    mut v___x_5211_: *mut LeanObject,
    mut v___x_5212_: *mut LeanObject,
    mut v_as_5213_: *mut LeanObject,
    mut v_sz_5214_: *mut LeanObject,
    mut v_i_5215_: *mut LeanObject,
    mut v_b_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5219_: usize = 0;
    let mut v_i_boxed_5220_: usize = 0;
    let mut v_res_5221_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5219_ = lean_unbox_usize(v_sz_5214_);
    lean_dec(v_sz_5214_);
    v_i_boxed_5220_ = lean_unbox_usize(v_i_5215_);
    lean_dec(v_i_5215_);
    v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_5207_, v_kind_5208_, v___x_5209_, v_params_5210_, v___x_5211_, v___x_5212_, v_as_5213_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5216_, v___y_5217_);
    lean_dec_ref(v___y_5217_);
    lean_dec_ref(v_as_5213_);
    lean_dec(v___x_5212_);
    return v_res_5221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(
    mut v_a_5225_: *mut LeanObject,
    mut v_as_5226_: *mut LeanObject,
    mut v_sz_5227_: usize,
    mut v_i_5228_: usize,
    mut v_b_5229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: usize = 0;
    let mut v___x_5235_: u8 = 0;
    let mut v_a_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExactMatch_5238_: u8 = 0;
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
                if v___x_5235_ == 0 {
                    lean_dec_ref(v_a_5225_);
                    lean_inc_ref(v_b_5229_);
                    return v_b_5229_;
                } else {
                    v_a_5236_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
                    v_decl_5237_ = lean_ctor_get(v_a_5236_, 1);
                    v_isExactMatch_5238_ = lean_ctor_get_uint8(
                        v_a_5236_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_5239_ = lean_box(0);
                    v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                    if v_isExactMatch_5238_ == 0 {
                        v_a_5231_ = v___x_5240_;
                        state = 1;
                        continue;
                    } else {
                        v_ctx_5241_ = lean_ctor_get(v_a_5225_, 1);
                        v_toCommandContextInfo_5242_ = lean_ctor_get(v_ctx_5241_, 0);
                        v_env_5243_ = lean_ctor_get(v_toCommandContextInfo_5242_, 0);
                        lean_inc(v_decl_5237_);
                        lean_inc_ref(v_env_5243_);
                        v___x_5244_ = l_Lean_Environment_contains(
                            v_env_5243_,
                            v_decl_5237_,
                            v_isExactMatch_5238_,
                        );
                        if v___x_5244_ == 0 {
                            lean_dec_ref(v_a_5225_);
                            lean_inc(v_a_5236_);
                            v___x_5245_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5245_, 0, v_a_5236_);
                            v___x_5246_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5246_, 0, v___x_5245_);
                            v___x_5247_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                            lean_ctor_set(v___x_5247_, 1, v___x_5239_);
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
    mut v_a_5248_: *mut LeanObject,
    mut v_as_5249_: *mut LeanObject,
    mut v_sz_5250_: *mut LeanObject,
    mut v_i_5251_: *mut LeanObject,
    mut v_b_5252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5253_: usize = 0;
    let mut v_i_boxed_5254_: usize = 0;
    let mut v_res_5255_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5253_ = lean_unbox_usize(v_sz_5250_);
    lean_dec(v_sz_5250_);
    v_i_boxed_5254_ = lean_unbox_usize(v_i_5251_);
    lean_dec(v_i_5251_);
    v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5248_, v_as_5249_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5252_);
    lean_dec_ref(v_b_5252_);
    lean_dec_ref(v_as_5249_);
    return v_res_5255_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(
    mut v_a_5256_: *mut LeanObject,
    mut v_x_5257_: *mut LeanObject,
) -> u8 {
    let mut v___x_5258_: u8 = 0;
    let mut v_key_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5257_) == 0 {
                    v___x_5258_ = 0;
                    return v___x_5258_;
                } else {
                    v_key_5259_ = lean_ctor_get(v_x_5257_, 0);
                    v_tail_5260_ = lean_ctor_get(v_x_5257_, 2);
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
    mut v_a_5263_: *mut LeanObject,
    mut v_x_5264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5265_: u8 = 0;
    let mut v_r_5266_: *mut LeanObject = core::ptr::null_mut();
    v_res_5265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5263_, v_x_5264_);
    lean_dec(v_x_5264_);
    lean_dec(v_a_5263_);
    v_r_5266_ = lean_box((v_res_5265_) as usize);
    return v_r_5266_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u64 = 0;
    v___x_5267_ = lean_unsigned_to_nat(1723);
    v___x_5268_ = lean_uint64_of_nat(v___x_5267_);
    return v___x_5268_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(
    mut v_m_5269_: *mut LeanObject,
    mut v_a_5270_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: u64 = 0;
    let mut v_hash_5289_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5271_ = lean_ctor_get(v_m_5269_, 1);
                v___x_5272_ = lean_array_get_size(v_buckets_5271_);
                if lean_obj_tag(v_a_5270_) == 0 {
                    v___x_5288_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5274_ = v___x_5288_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5289_ = lean_ctor_get_uint64(
                        v_a_5270_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5292_: u8 = 0;
    let mut v_r_5293_: *mut LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5290_, v_a_5291_);
    lean_dec(v_a_5291_);
    lean_dec_ref(v_m_5290_);
    v_r_5293_ = lean_box((v_res_5292_) as usize);
    return v_r_5293_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(
    mut v_x_5294_: *mut LeanObject,
    mut v_x_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u64 = 0;
    let mut v_hash_5323_: u64 = 0;
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5295_) == 0 {
                    return v_x_5294_;
                } else {
                    v_key_5296_ = lean_ctor_get(v_x_5295_, 0);
                    v_value_5297_ = lean_ctor_get(v_x_5295_, 1);
                    v_tail_5298_ = lean_ctor_get(v_x_5295_, 2);
                    v_isSharedCheck_5324_ = (!lean_is_exclusive(v_x_5295_)) as u8;
                    if v_isSharedCheck_5324_ == 0 {
                        v___x_5300_ = v_x_5295_;
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5298_);
                        lean_inc(v_value_5297_);
                        lean_inc(v_key_5296_);
                        lean_dec(v_x_5295_);
                        v___x_5300_ = lean_box(0);
                        v_isShared_5301_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5302_ = lean_array_get_size(v_x_5294_);
                if lean_obj_tag(v_key_5296_) == 0 {
                    v___x_5322_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5304_ = v___x_5322_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5323_ = lean_ctor_get_uint64(
                        v_key_5296_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_5316_);
                if v_isShared_5301_ == 0 {
                    lean_ctor_set(v___x_5300_, 2, v___x_5316_);
                    v___x_5318_ = v___x_5300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_key_5296_);
                    lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_value_5297_);
                    lean_ctor_set(v_reuseFailAlloc_5321_, 2, v___x_5316_);
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
    mut v_i_5325_: *mut LeanObject,
    mut v_source_5326_: *mut LeanObject,
    mut v_target_5327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: u8 = 0;
    let mut v_es_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5328_ = lean_array_get_size(v_source_5326_);
                v___x_5329_ = lean_nat_dec_lt(v_i_5325_, v___x_5328_);
                if v___x_5329_ == 0 {
                    lean_dec_ref(v_source_5326_);
                    lean_dec(v_i_5325_);
                    return v_target_5327_;
                } else {
                    v_es_5330_ = lean_array_fget(v_source_5326_, v_i_5325_);
                    v___x_5331_ = lean_box(0);
                    v_source_5332_ = lean_array_fset(v_source_5326_, v_i_5325_, v___x_5331_);
                    v_target_5333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_5327_, v_es_5330_);
                    v___x_5334_ = lean_unsigned_to_nat(1);
                    v___x_5335_ = lean_nat_add(v_i_5325_, v___x_5334_);
                    lean_dec(v_i_5325_);
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
    mut v_data_5337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    v___x_5338_ = lean_array_get_size(v_data_5337_);
    v___x_5339_ = lean_unsigned_to_nat(2);
    v_nbuckets_5340_ = lean_nat_mul(v___x_5338_, v___x_5339_);
    v___x_5341_ = lean_unsigned_to_nat(0);
    v___x_5342_ = lean_box(0);
    v___x_5343_ = lean_mk_array(v_nbuckets_5340_, v___x_5342_);
    v___x_5344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_5341_, v_data_5337_, v___x_5343_);
    return v___x_5344_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(
    mut v_m_5345_: *mut LeanObject,
    mut v_a_5346_: *mut LeanObject,
    mut v_b_5347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v_val_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_unused_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: u64 = 0;
    let mut v_hash_5390_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5348_ = lean_ctor_get(v_m_5345_, 0);
                v_buckets_5349_ = lean_ctor_get(v_m_5345_, 1);
                v___x_5350_ = lean_array_get_size(v_buckets_5349_);
                if lean_obj_tag(v_a_5346_) == 0 {
                    v___x_5389_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
                    v___y_5352_ = v___x_5389_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5390_ = lean_ctor_get_uint64(
                        v_a_5346_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_inc_ref(v_buckets_5349_);
                    lean_inc(v_size_5348_);
                    v_isSharedCheck_5386_ = (!lean_is_exclusive(v_m_5345_)) as u8;
                    if v_isSharedCheck_5386_ == 0 {
                        v_unused_5387_ = lean_ctor_get(v_m_5345_, 1);
                        lean_dec(v_unused_5387_);
                        v_unused_5388_ = lean_ctor_get(v_m_5345_, 0);
                        lean_dec(v_unused_5388_);
                        v___x_5367_ = v_m_5345_;
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_5345_);
                        v___x_5367_ = lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5347_);
                    lean_dec(v_a_5346_);
                    return v_m_5345_;
                }
            }
            2 => {
                v___x_5369_ = lean_unsigned_to_nat(1);
                v_size_x27_5370_ = lean_nat_add(v_size_5348_, v___x_5369_);
                lean_dec(v_size_5348_);
                lean_inc(v_bkt_5364_);
                v___x_5371_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5371_, 0, v_a_5346_);
                lean_ctor_set(v___x_5371_, 1, v_b_5347_);
                lean_ctor_set(v___x_5371_, 2, v_bkt_5364_);
                v_buckets_x27_5372_ = lean_array_uset(v_buckets_5349_, v___x_5363_, v___x_5371_);
                v___x_5373_ = lean_unsigned_to_nat(4);
                v___x_5374_ = lean_nat_mul(v_size_x27_5370_, v___x_5373_);
                v___x_5375_ = lean_unsigned_to_nat(3);
                v___x_5376_ = lean_nat_div(v___x_5374_, v___x_5375_);
                lean_dec(v___x_5374_);
                v___x_5377_ = lean_array_get_size(v_buckets_x27_5372_);
                v___x_5378_ = lean_nat_dec_le(v___x_5376_, v___x_5377_);
                lean_dec(v___x_5376_);
                if v___x_5378_ == 0 {
                    v_val_5379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_5372_);
                    if v_isShared_5368_ == 0 {
                        lean_ctor_set(v___x_5367_, 1, v_val_5379_);
                        lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5381_ = v___x_5367_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_size_x27_5370_);
                        lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_val_5379_);
                        v___x_5381_ = v_reuseFailAlloc_5382_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_5368_ == 0 {
                        lean_ctor_set(v___x_5367_, 1, v_buckets_x27_5372_);
                        lean_ctor_set(v___x_5367_, 0, v_size_x27_5370_);
                        v___x_5384_ = v___x_5367_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_size_x27_5370_);
                        lean_ctor_set(v_reuseFailAlloc_5385_, 1, v_buckets_x27_5372_);
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
    mut v___x_5391_: *mut LeanObject,
    mut v_as_5392_: *mut LeanObject,
    mut v_sz_5393_: usize,
    mut v_i_5394_: usize,
    mut v_b_5395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: usize = 0;
    let mut v___x_5400_: usize = 0;
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v_fst_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v_array_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v_a_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5433_: usize = 0;
    let mut v___x_5434_: usize = 0;
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_determineInsertion_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_edits_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_edit_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_unused_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5488_: u8 = 0;
    let mut v_unused_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5490_: u8 = 0;
    let mut v_unused_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_unused_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5496_: u8 = 0;
    let mut v_unused_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5402_ = lean_usize_dec_lt(v_i_5394_, v_sz_5393_);
                if v___x_5402_ == 0 {
                    lean_dec_ref(v___x_5391_);
                    v___x_5403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5403_, 0, v_b_5395_);
                    return v___x_5403_;
                } else {
                    v_snd_5404_ = lean_ctor_get(v_b_5395_, 1);
                    lean_inc(v_snd_5404_);
                    v_snd_5405_ = lean_ctor_get(v_snd_5404_, 1);
                    lean_inc(v_snd_5405_);
                    v_fst_5406_ = lean_ctor_get(v_b_5395_, 0);
                    v_isSharedCheck_5496_ = (!lean_is_exclusive(v_b_5395_)) as u8;
                    if v_isSharedCheck_5496_ == 0 {
                        v_unused_5497_ = lean_ctor_get(v_b_5395_, 1);
                        lean_dec(v_unused_5497_);
                        v___x_5408_ = v_b_5395_;
                        v_isShared_5409_ = v_isSharedCheck_5496_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_5406_);
                        lean_dec(v_b_5395_);
                        v___x_5408_ = lean_box(0);
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
                v_fst_5410_ = lean_ctor_get(v_snd_5404_, 0);
                v_isSharedCheck_5494_ = (!lean_is_exclusive(v_snd_5404_)) as u8;
                if v_isSharedCheck_5494_ == 0 {
                    v_unused_5495_ = lean_ctor_get(v_snd_5404_, 1);
                    lean_dec(v_unused_5495_);
                    v___x_5412_ = v_snd_5404_;
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_5410_);
                    lean_dec(v_snd_5404_);
                    v___x_5412_ = lean_box(0);
                    v_isShared_5413_ = v_isSharedCheck_5494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_5414_ = lean_ctor_get(v_snd_5405_, 0);
                v_start_5415_ = lean_ctor_get(v_snd_5405_, 1);
                v_stop_5416_ = lean_ctor_get(v_snd_5405_, 2);
                v___x_5417_ = lean_nat_dec_lt(v_start_5415_, v_stop_5416_);
                if v___x_5417_ == 0 {
                    lean_dec_ref(v___x_5391_);
                    if v_isShared_5413_ == 0 {
                        v___x_5419_ = v___x_5412_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_fst_5410_);
                        lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_snd_5405_);
                        v___x_5419_ = v_reuseFailAlloc_5424_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_5416_);
                    lean_inc(v_start_5415_);
                    lean_inc_ref(v_array_5414_);
                    v_isSharedCheck_5490_ = (!lean_is_exclusive(v_snd_5405_)) as u8;
                    if v_isSharedCheck_5490_ == 0 {
                        v_unused_5491_ = lean_ctor_get(v_snd_5405_, 2);
                        lean_dec(v_unused_5491_);
                        v_unused_5492_ = lean_ctor_get(v_snd_5405_, 1);
                        lean_dec(v_unused_5492_);
                        v_unused_5493_ = lean_ctor_get(v_snd_5405_, 0);
                        lean_dec(v_unused_5493_);
                        v___x_5426_ = v_snd_5405_;
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_snd_5405_);
                        v___x_5426_ = lean_box(0);
                        v_isShared_5427_ = v_isSharedCheck_5490_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5409_ == 0 {
                    lean_ctor_set(v___x_5408_, 1, v___x_5419_);
                    v___x_5421_ = v___x_5408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_fst_5406_);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5419_);
                    v___x_5421_ = v_reuseFailAlloc_5423_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5422_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5422_, 0, v___x_5421_);
                return v___x_5422_;
            }
            6 => {
                v_a_5428_ = lean_array_uget_borrowed(v_as_5392_, v_i_5394_);
                v___x_5429_ = lean_array_fget_borrowed(v_array_5414_, v_start_5415_);
                v___x_5430_ = lean_box(0);
                v___x_5431_ = lean_box(0);
                v___x_5432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0;
                v_sz_5433_ = lean_array_size(v___x_5429_);
                v___x_5434_ = 0usize;
                lean_inc(v_a_5428_);
                v___x_5435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_5428_, v___x_5429_, v_sz_5433_, v___x_5434_, v___x_5432_);
                v_fst_5436_ = lean_ctor_get(v___x_5435_, 0);
                v_isSharedCheck_5488_ = (!lean_is_exclusive(v___x_5435_)) as u8;
                if v_isSharedCheck_5488_ == 0 {
                    v_unused_5489_ = lean_ctor_get(v___x_5435_, 1);
                    lean_dec(v_unused_5489_);
                    v___x_5438_ = v___x_5435_;
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_fst_5436_);
                    lean_dec(v___x_5435_);
                    v___x_5438_ = lean_box(0);
                    v_isShared_5439_ = v_isSharedCheck_5488_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5440_ = lean_unsigned_to_nat(1);
                v___x_5441_ = lean_nat_add(v_start_5415_, v___x_5440_);
                lean_dec(v_start_5415_);
                if v_isShared_5427_ == 0 {
                    lean_ctor_set(v___x_5426_, 1, v___x_5441_);
                    v___x_5443_ = v___x_5426_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_array_5414_);
                    lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5441_);
                    lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_stop_5416_);
                    v___x_5443_ = v_reuseFailAlloc_5487_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if lean_obj_tag(v_fst_5436_) == 0 {
                    lean_del_object(v___x_5408_);
                    state = 9;
                    continue;
                } else {
                    v_val_5451_ = lean_ctor_get(v_fst_5436_, 0);
                    lean_inc(v_val_5451_);
                    lean_dec_ref_known(v_fst_5436_, 1);
                    if lean_obj_tag(v_val_5451_) == 1 {
                        lean_del_object(v___x_5438_);
                        lean_del_object(v___x_5412_);
                        v_val_5452_ = lean_ctor_get(v_val_5451_, 0);
                        lean_inc(v_val_5452_);
                        lean_dec_ref_known(v_val_5451_, 1);
                        v_ctx_5453_ = lean_ctor_get(v_a_5428_, 1);
                        v_toCommandContextInfo_5454_ = lean_ctor_get(v_ctx_5453_, 0);
                        v_module_5455_ = lean_ctor_get(v_val_5452_, 0);
                        lean_inc(v_module_5455_);
                        v_decl_5456_ = lean_ctor_get(v_val_5452_, 1);
                        lean_inc(v_decl_5456_);
                        lean_dec(v_val_5452_);
                        v_determineInsertion_5457_ = lean_ctor_get(v_a_5428_, 2);
                        v_env_5458_ = lean_ctor_get(v_toCommandContextInfo_5454_, 0);
                        v___x_5459_ = l_Lean_Environment_mainModule(v_env_5458_);
                        v___x_5460_ = lean_name_eq(v_module_5455_, v___x_5459_);
                        lean_dec(v___x_5459_);
                        if v___x_5460_ == 0 {
                            lean_inc_ref(v_determineInsertion_5457_);
                            v___x_5461_ = lean_apply_1(v_determineInsertion_5457_, v_decl_5456_);
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
                            lean_dec(v_decl_5456_);
                            lean_dec(v_module_5455_);
                            if v_isShared_5409_ == 0 {
                                lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                                lean_ctor_set(v___x_5408_, 0, v_fst_5410_);
                                v___x_5484_ = v___x_5408_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_fst_5410_);
                                lean_ctor_set(v_reuseFailAlloc_5486_, 1, v___x_5443_);
                                v___x_5484_ = v_reuseFailAlloc_5486_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_5451_);
                        lean_del_object(v___x_5408_);
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5439_ == 0 {
                    lean_ctor_set(v___x_5438_, 1, v___x_5443_);
                    lean_ctor_set(v___x_5438_, 0, v_fst_5410_);
                    v___x_5446_ = v___x_5438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_fst_5410_);
                    lean_ctor_set(v_reuseFailAlloc_5450_, 1, v___x_5443_);
                    v___x_5446_ = v_reuseFailAlloc_5450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5413_ == 0 {
                    lean_ctor_set(v___x_5412_, 1, v___x_5446_);
                    lean_ctor_set(v___x_5412_, 0, v_fst_5406_);
                    v___x_5448_ = v___x_5412_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5406_);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5446_);
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
                v_edit_5464_ = lean_ctor_get(v___x_5461_, 1);
                v_isSharedCheck_5476_ = (!lean_is_exclusive(v___x_5461_)) as u8;
                if v_isSharedCheck_5476_ == 0 {
                    v_unused_5477_ = lean_ctor_get(v___x_5461_, 0);
                    lean_dec(v_unused_5477_);
                    v___x_5466_ = v___x_5461_;
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_edit_5464_);
                    lean_dec(v___x_5461_);
                    v___x_5466_ = lean_box(0);
                    v_isShared_5467_ = v_isSharedCheck_5476_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5468_ = lean_array_push(v_edits_5463_, v_edit_5464_);
                v___x_5469_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_5410_, v_module_5455_, v___x_5431_);
                if v_isShared_5409_ == 0 {
                    lean_ctor_set(v___x_5408_, 1, v___x_5443_);
                    lean_ctor_set(v___x_5408_, 0, v___x_5469_);
                    v___x_5471_ = v___x_5408_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5469_);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 1, v___x_5443_);
                    v___x_5471_ = v_reuseFailAlloc_5475_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5467_ == 0 {
                    lean_ctor_set(v___x_5466_, 1, v___x_5471_);
                    lean_ctor_set(v___x_5466_, 0, v___x_5468_);
                    v___x_5473_ = v___x_5466_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5468_);
                    lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5471_);
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
                lean_inc(v_module_5455_);
                lean_inc_ref(v_ctx_5453_);
                v___x_5479_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_5453_, v_module_5455_);
                lean_inc_ref(v___x_5391_);
                v___x_5480_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5480_, 0, v___x_5391_);
                lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                lean_ctor_set(v___x_5480_, 2, v___x_5430_);
                lean_ctor_set(v___x_5480_, 3, v___x_5430_);
                v___x_5481_ = lean_array_push(v_fst_5406_, v___x_5480_);
                v_edits_5463_ = v___x_5481_;
                state = 12;
                continue;
            }
            17 => {
                v___x_5485_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5485_, 0, v_fst_5406_);
                lean_ctor_set(v___x_5485_, 1, v___x_5484_);
                v_a_5398_ = v___x_5485_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(
    mut v___x_5498_: *mut LeanObject,
    mut v_as_5499_: *mut LeanObject,
    mut v_sz_5500_: *mut LeanObject,
    mut v_i_5501_: *mut LeanObject,
    mut v_b_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5504_: usize = 0;
    let mut v_i_boxed_5505_: usize = 0;
    let mut v_res_5506_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5504_ = lean_unbox_usize(v_sz_5500_);
    lean_dec(v_sz_5500_);
    v_i_boxed_5505_ = lean_unbox_usize(v_i_5501_);
    lean_dec(v_i_5501_);
    v_res_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5498_, v_as_5499_, v_sz_boxed_5504_, v_i_boxed_5505_, v_b_5502_);
    lean_dec_ref(v_as_5499_);
    return v_res_5506_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(
    mut v___x_5507_: *mut LeanObject,
    mut v_as_5508_: *mut LeanObject,
    mut v_i_5509_: usize,
    mut v_stop_5510_: usize,
    mut v_b_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: usize = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5519_ = lean_usize_dec_eq(v_i_5509_, v_stop_5510_);
                if v___x_5519_ == 0 {
                    v___x_5520_ = lean_array_uget_borrowed(v_as_5508_, v_i_5509_);
                    v_stop_5521_ = lean_ctor_get(v___x_5520_, 1);
                    lean_inc(v_stop_5521_);
                    lean_inc_ref(v___x_5507_);
                    v___x_5522_ = l_Lean_Server_FileWorker_computeQueries(
                        v___x_5507_,
                        v_stop_5521_,
                        v___y_5512_,
                    );
                    if lean_obj_tag(v___x_5522_) == 0 {
                        v_a_5523_ = lean_ctor_get(v___x_5522_, 0);
                        lean_inc(v_a_5523_);
                        lean_dec_ref_known(v___x_5522_, 1);
                        v___x_5524_ = l_Array_append___redArg(v_b_5511_, v_a_5523_);
                        lean_dec(v_a_5523_);
                        v_a_5515_ = v___x_5524_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_5511_);
                        if lean_obj_tag(v___x_5522_) == 0 {
                            v_a_5525_ = lean_ctor_get(v___x_5522_, 0);
                            lean_inc(v_a_5525_);
                            lean_dec_ref_known(v___x_5522_, 1);
                            v_a_5515_ = v_a_5525_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_5507_);
                            return v___x_5522_;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5507_);
                    v___x_5526_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5526_, 0, v_b_5511_);
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
    mut v___x_5527_: *mut LeanObject,
    mut v_as_5528_: *mut LeanObject,
    mut v_i_5529_: *mut LeanObject,
    mut v_stop_5530_: *mut LeanObject,
    mut v_b_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5534_: usize = 0;
    let mut v_stop_boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5534_ = lean_unbox_usize(v_i_5529_);
    lean_dec(v_i_5529_);
    v_stop_boxed_5535_ = lean_unbox_usize(v_stop_5530_);
    lean_dec(v_stop_5530_);
    v_res_5536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_5527_, v_as_5528_, v_i_boxed_5534_, v_stop_boxed_5535_, v_b_5531_, v___y_5532_);
    lean_dec_ref(v___y_5532_);
    lean_dec_ref(v_as_5528_);
    return v_res_5536_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0()
-> *mut LeanObject {
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    v___x_5537_ = lean_box(0);
    v___x_5538_ = lean_unsigned_to_nat(16);
    v___x_5539_ = lean_mk_array(v___x_5538_, v___x_5537_);
    return v___x_5539_;
}
pub unsafe fn l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
    mut v_id_5542_: *mut LeanObject,
    mut v_action_5543_: *mut LeanObject,
    mut v_unknownIdentifierRanges_5544_: *mut LeanObject,
    mut v_a_5545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_doc_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: usize = 0;
    let mut v___y_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: usize = 0;
    let mut v___y_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v_fst_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v_toWorkDoneProgressParams_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_title_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_x3f_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreferred_x3f_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disabled_x3f_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_command_x3f_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_unused_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_unused_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_a_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut v_toEditableDocumentCore_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSnap_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5620_: usize = 0;
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_response_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut v_unused_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: u8 = 0;
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5547_ = lean_ctor_get(v_a_5545_, 1);
                v_toEditableDocumentCore_5610_ = lean_ctor_get(v_doc_5547_, 0);
                v_meta_5611_ = lean_ctor_get(v_toEditableDocumentCore_5610_, 0);
                v_initSnap_5612_ = lean_ctor_get(v_toEditableDocumentCore_5610_, 1);
                v_text_5613_ = lean_ctor_get(v_meta_5611_, 3);
                v___x_5665_ = lean_unsigned_to_nat(0);
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
                            lean_inc_ref(v_doc_5547_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5670_, v___x_5671_, v___x_5666_, v_a_5545_);
                            v___y_5655_ = v___x_5672_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_5673_ = 0usize;
                        v___x_5674_ = lean_usize_of_nat(v___x_5667_);
                        lean_inc_ref(v_doc_5547_);
                        v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_5547_, v_unknownIdentifierRanges_5544_, v___x_5673_, v___x_5674_, v___x_5666_, v_a_5545_);
                        v___y_5655_ = v___x_5675_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_5554_);
                v___x_5555_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5555_, 0, v___y_5554_);
                lean_ctor_set(v___x_5555_, 1, v___y_5554_);
                v___x_5556_ = lean_mk_empty_array_with_capacity(v___y_5552_);
                v___x_5557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once), _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
                lean_inc(v___y_5552_);
                v___x_5558_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5558_, 0, v___y_5552_);
                lean_ctor_set(v___x_5558_, 1, v___x_5557_);
                v___x_5559_ = lean_array_get_size(v___y_5553_);
                v___x_5560_ = l_Array_toSubarray___redArg(v___y_5553_, v___y_5552_, v___x_5559_);
                v___x_5561_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5561_, 0, v___x_5558_);
                lean_ctor_set(v___x_5561_, 1, v___x_5560_);
                v___x_5562_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5562_, 0, v___x_5556_);
                lean_ctor_set(v___x_5562_, 1, v___x_5561_);
                v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5555_, v___y_5550_, v___y_5549_, v___y_5551_, v___x_5562_);
                lean_dec_ref(v___y_5550_);
                if lean_obj_tag(v___x_5563_) == 0 {
                    v_a_5564_ = lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5601_ = (!lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5601_ == 0 {
                        v___x_5566_ = v___x_5563_;
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5564_);
                        lean_dec(v___x_5563_);
                        v___x_5566_ = lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5601_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_action_5543_);
                    v_a_5602_ = lean_ctor_get(v___x_5563_, 0);
                    v_isSharedCheck_5609_ = (!lean_is_exclusive(v___x_5563_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v___x_5563_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5602_);
                        lean_dec(v___x_5563_);
                        v___x_5604_ = lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5568_ = lean_ctor_get(v_a_5564_, 0);
                v_isSharedCheck_5599_ = (!lean_is_exclusive(v_a_5564_)) as u8;
                if v_isSharedCheck_5599_ == 0 {
                    v_unused_5600_ = lean_ctor_get(v_a_5564_, 1);
                    lean_dec(v_unused_5600_);
                    v___x_5570_ = v_a_5564_;
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_5568_);
                    lean_dec(v_a_5564_);
                    v___x_5570_ = lean_box(0);
                    v_isShared_5571_ = v_isSharedCheck_5599_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toWorkDoneProgressParams_5572_ = lean_ctor_get(v_action_5543_, 0);
                v_toPartialResultParams_5573_ = lean_ctor_get(v_action_5543_, 1);
                v_title_5574_ = lean_ctor_get(v_action_5543_, 2);
                v_kind_x3f_5575_ = lean_ctor_get(v_action_5543_, 3);
                v_diagnostics_x3f_5576_ = lean_ctor_get(v_action_5543_, 4);
                v_isPreferred_x3f_5577_ = lean_ctor_get(v_action_5543_, 5);
                v_disabled_x3f_5578_ = lean_ctor_get(v_action_5543_, 6);
                v_command_x3f_5579_ = lean_ctor_get(v_action_5543_, 8);
                v_data_x3f_5580_ = lean_ctor_get(v_action_5543_, 9);
                v_isSharedCheck_5597_ = (!lean_is_exclusive(v_action_5543_)) as u8;
                if v_isSharedCheck_5597_ == 0 {
                    v_unused_5598_ = lean_ctor_get(v_action_5543_, 7);
                    lean_dec(v_unused_5598_);
                    v___x_5582_ = v_action_5543_;
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_data_x3f_5580_);
                    lean_inc(v_command_x3f_5579_);
                    lean_inc(v_disabled_x3f_5578_);
                    lean_inc(v_isPreferred_x3f_5577_);
                    lean_inc(v_diagnostics_x3f_5576_);
                    lean_inc(v_kind_x3f_5575_);
                    lean_inc(v_title_5574_);
                    lean_inc(v_toPartialResultParams_5573_);
                    lean_inc(v_toWorkDoneProgressParams_5572_);
                    lean_dec(v_action_5543_);
                    v___x_5582_ = lean_box(0);
                    v_isShared_5583_ = v_isSharedCheck_5597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_doc_5547_);
                v___x_5584_ =
                    l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_5547_);
                if v_isShared_5571_ == 0 {
                    lean_ctor_set(v___x_5570_, 1, v_fst_5568_);
                    lean_ctor_set(v___x_5570_, 0, v___x_5584_);
                    v___x_5586_ = v___x_5570_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5584_);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_fst_5568_);
                    v___x_5586_ = v_reuseFailAlloc_5596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5587_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_5586_);
                v___x_5588_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5588_, 0, v___x_5587_);
                if v_isShared_5583_ == 0 {
                    lean_ctor_set(v___x_5582_, 7, v___x_5588_);
                    v___x_5590_ = v___x_5582_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_toWorkDoneProgressParams_5572_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 1, v_toPartialResultParams_5573_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_title_5574_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 3, v_kind_x3f_5575_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 4, v_diagnostics_x3f_5576_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 5, v_isPreferred_x3f_5577_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 6, v_disabled_x3f_5578_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 7, v___x_5588_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 8, v_command_x3f_5579_);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 9, v_data_x3f_5580_);
                    v___x_5590_ = v_reuseFailAlloc_5595_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5591_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5591_, 0, v___x_5590_);
                if v_isShared_5567_ == 0 {
                    lean_ctor_set(v___x_5566_, 0, v___x_5591_);
                    v___x_5593_ = v___x_5566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5591_);
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
                    v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
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
                v___x_5617_ = lean_unsigned_to_nat(0);
                v___x_5618_ = lean_nat_dec_eq(v___x_5616_, v___x_5617_);
                if v___x_5618_ == 0 {
                    v___x_5619_ =
                        l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
                    v_sz_5620_ = lean_array_size(v_a_5615_);
                    v___x_5621_ = 0usize;
                    lean_inc_ref(v_a_5615_);
                    v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_5620_, v___x_5621_, v_a_5615_);
                    v___x_5623_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5623_, 0, v_id_5542_);
                    lean_ctor_set(v___x_5623_, 1, v___x_5622_);
                    v___x_5624_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_5619_, v___x_5623_, v_a_5545_);
                    v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5651_ = (!lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5651_ == 0 {
                        v___x_5627_ = v___x_5624_;
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5625_);
                        lean_dec(v___x_5624_);
                        v___x_5627_ = lean_box(0);
                        v_isShared_5628_ = v_isSharedCheck_5651_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_5615_);
                    lean_dec_ref(v_action_5543_);
                    lean_dec(v_id_5542_);
                    v___x_5652_ = lean_box(0);
                    v___x_5653_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5653_, 0, v___x_5652_);
                    return v___x_5653_;
                }
            }
            11 => {
                v___x_5629_ = lean_task_get_own(v_a_5625_);
                if lean_obj_tag(v___x_5629_) == 0 {
                    lean_del_object(v___x_5627_);
                    v_response_5630_ = lean_ctor_get(v___x_5629_, 0);
                    lean_inc(v_response_5630_);
                    lean_dec_ref_known(v___x_5629_, 1);
                    v_stx_5631_ = lean_ctor_get(v_initSnap_5612_, 3);
                    v___x_5632_ = l_Lean_Syntax_getTailPos_x3f(v_stx_5631_, v___x_5618_);
                    if lean_obj_tag(v___x_5632_) == 0 {
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
                        v_val_5634_ = lean_ctor_get(v___x_5632_, 0);
                        lean_inc(v_val_5634_);
                        lean_dec_ref_known(v___x_5632_, 1);
                        lean_inc_ref(v_text_5613_);
                        v___x_5635_ = l_Lean_FileMap_utf8PosToLspPos(v_text_5613_, v_val_5634_);
                        lean_dec(v_val_5634_);
                        v_line_5636_ = lean_ctor_get(v___x_5635_, 0);
                        v_isSharedCheck_5645_ = (!lean_is_exclusive(v___x_5635_)) as u8;
                        if v_isSharedCheck_5645_ == 0 {
                            v_unused_5646_ = lean_ctor_get(v___x_5635_, 1);
                            lean_dec(v_unused_5646_);
                            v___x_5638_ = v___x_5635_;
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_line_5636_);
                            lean_dec(v___x_5635_);
                            v___x_5638_ = lean_box(0);
                            v_isShared_5639_ = v_isSharedCheck_5645_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5629_);
                    lean_dec_ref(v_a_5615_);
                    lean_dec_ref(v_action_5543_);
                    v___x_5647_ = lean_box(0);
                    if v_isShared_5628_ == 0 {
                        lean_ctor_set(v___x_5627_, 0, v___x_5647_);
                        v___x_5649_ = v___x_5627_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5647_);
                        v___x_5649_ = v_reuseFailAlloc_5650_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5640_ = lean_unsigned_to_nat(1);
                v___x_5641_ = lean_nat_add(v_line_5636_, v___x_5640_);
                lean_dec(v_line_5636_);
                if v_isShared_5639_ == 0 {
                    lean_ctor_set(v___x_5638_, 1, v___x_5617_);
                    lean_ctor_set(v___x_5638_, 0, v___x_5641_);
                    v___x_5643_ = v___x_5638_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5641_);
                    lean_ctor_set(v_reuseFailAlloc_5644_, 1, v___x_5617_);
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
                if lean_obj_tag(v___y_5655_) == 0 {
                    v_a_5656_ = lean_ctor_get(v___y_5655_, 0);
                    lean_inc(v_a_5656_);
                    lean_dec_ref_known(v___y_5655_, 1);
                    v_a_5615_ = v_a_5656_;
                    state = 10;
                    continue;
                } else {
                    lean_dec_ref(v_action_5543_);
                    lean_dec(v_id_5542_);
                    v_a_5657_ = lean_ctor_get(v___y_5655_, 0);
                    v_isSharedCheck_5664_ = (!lean_is_exclusive(v___y_5655_)) as u8;
                    if v_isSharedCheck_5664_ == 0 {
                        v___x_5659_ = v___y_5655_;
                        v_isShared_5660_ = v_isSharedCheck_5664_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5657_);
                        lean_dec(v___y_5655_);
                        v___x_5659_ = lean_box(0);
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
                    v_reuseFailAlloc_5663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_a_5657_);
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
    mut v_id_5676_: *mut LeanObject,
    mut v_action_5677_: *mut LeanObject,
    mut v_unknownIdentifierRanges_5678_: *mut LeanObject,
    mut v_a_5679_: *mut LeanObject,
    mut v_a_5680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5681_: *mut LeanObject = core::ptr::null_mut();
    v_res_5681_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(
        v_id_5676_,
        v_action_5677_,
        v_unknownIdentifierRanges_5678_,
        v_a_5679_,
    );
    lean_dec_ref(v_a_5679_);
    lean_dec_ref(v_unknownIdentifierRanges_5678_);
    return v_res_5681_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(
    mut v_00_u03b2_5682_: *mut LeanObject,
    mut v_m_5683_: *mut LeanObject,
    mut v_a_5684_: *mut LeanObject,
    mut v_b_5685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_5683_, v_a_5684_, v_b_5685_);
    return v___x_5686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(
    mut v_00_u03b2_5687_: *mut LeanObject,
    mut v_m_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
) -> u8 {
    let mut v___x_5690_: u8 = 0;
    v___x_5690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_5688_, v_a_5689_);
    return v___x_5690_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(
    mut v_00_u03b2_5691_: *mut LeanObject,
    mut v_m_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5694_: u8 = 0;
    let mut v_r_5695_: *mut LeanObject = core::ptr::null_mut();
    v_res_5694_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_5691_, v_m_5692_, v_a_5693_);
    lean_dec(v_a_5693_);
    lean_dec_ref(v_m_5692_);
    v_r_5695_ = lean_box((v_res_5694_) as usize);
    return v_r_5695_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(
    mut v___x_5696_: *mut LeanObject,
    mut v_as_5697_: *mut LeanObject,
    mut v_sz_5698_: usize,
    mut v_i_5699_: usize,
    mut v_b_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_5696_, v_as_5697_, v_sz_5698_, v_i_5699_, v_b_5700_);
    return v___x_5703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(
    mut v___x_5704_: *mut LeanObject,
    mut v_as_5705_: *mut LeanObject,
    mut v_sz_5706_: *mut LeanObject,
    mut v_i_5707_: *mut LeanObject,
    mut v_b_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5711_: usize = 0;
    let mut v_i_boxed_5712_: usize = 0;
    let mut v_res_5713_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5711_ = lean_unbox_usize(v_sz_5706_);
    lean_dec(v_sz_5706_);
    v_i_boxed_5712_ = lean_unbox_usize(v_i_5707_);
    lean_dec(v_i_5707_);
    v_res_5713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_5704_, v_as_5705_, v_sz_boxed_5711_, v_i_boxed_5712_, v_b_5708_, v___y_5709_);
    lean_dec_ref(v___y_5709_);
    lean_dec_ref(v_as_5705_);
    return v_res_5713_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(
    mut v_00_u03b2_5714_: *mut LeanObject,
    mut v_a_5715_: *mut LeanObject,
    mut v_x_5716_: *mut LeanObject,
) -> u8 {
    let mut v___x_5717_: u8 = 0;
    v___x_5717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_5715_, v_x_5716_);
    return v___x_5717_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_5718_: *mut LeanObject,
    mut v_a_5719_: *mut LeanObject,
    mut v_x_5720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5721_: u8 = 0;
    let mut v_r_5722_: *mut LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_5718_, v_a_5719_, v_x_5720_);
    lean_dec(v_x_5720_);
    lean_dec(v_a_5719_);
    v_r_5722_ = lean_box((v_res_5721_) as usize);
    return v_r_5722_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(
    mut v_00_u03b2_5723_: *mut LeanObject,
    mut v_data_5724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    v___x_5725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_5724_);
    return v___x_5725_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5726_: *mut LeanObject,
    mut v_i_5727_: *mut LeanObject,
    mut v_source_5728_: *mut LeanObject,
    mut v_target_5729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    v___x_5730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_5727_, v_source_5728_, v_target_5729_);
    return v___x_5730_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(
    mut v_00_u03b2_5731_: *mut LeanObject,
    mut v_x_5732_: *mut LeanObject,
    mut v_x_5733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    v___x_5734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_5732_, v_x_5733_);
    return v___x_5734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
}
