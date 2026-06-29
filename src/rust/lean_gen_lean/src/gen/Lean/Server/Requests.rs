// Lean compiler output
// Module: Lean.Server.Requests
// Imports: Lean.Server.RequestCancellation Lean.Server.FileSource Lean.Server.FileWorker.Utils Std.Sync.Mutex
use crate::r#gen::Init::Control::Except::l_Except_map;
use crate::r#gen::Init::Control::Reader::l_ReaderT_tryFinally___redArg___lam__1;
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_get___boxed, l_StateRefT_x27_instMonad___aux__13___boxed,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_ReaderT_instMonad___redArg, l_String_hash___boxed,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqString___boxed,
    l_instMonadLiftT___lam__0___boxed, l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::IO::{
    l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, l_instMonadEIO,
    l_instMonadFinallyEIO___aux__1___boxed, l_instMonadLiftBaseIOEIO___lam__0___boxed,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_contains___redArg, l_Lean_PersistentHashMap_insert___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_toMessageData;
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Language::Lean::Types::l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_toString, l_Lean_MessageLog_append, l_Lean_MessageLog_empty,
};
use crate::r#gen::Lean::Server::AsyncList::l_IO_AsyncList_waitFind_x3f___redArg;
use crate::r#gen::Lean::Server::FileSource::{
    initialize_Lean_Server_FileSource, runtime_initialize_Lean_Server_FileSource,
};
use crate::r#gen::Lean::Server::FileWorker::Utils::{
    initialize_Lean_Server_FileWorker_Utils, runtime_initialize_Lean_Server_FileWorker_Utils,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    l_Lean_Elab_Info_range_x3f, l_Lean_Elab_InfoTree_foldInfo___redArg,
};
use crate::r#gen::Lean::Server::RequestCancellation::{
    initialize_Lean_Server_RequestCancellation,
    l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest,
    runtime_initialize_Lean_Server_RequestCancellation,
};
use crate::r#gen::Lean::Server::ServerTask::{
    l_Lean_Server_ServerTask_EIO_asTask___redArg,
    l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg,
    l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg,
    l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg,
    l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg,
    l_Lean_Server_ServerTask_bindCheap___redArg, l_Lean_Server_ServerTask_mapCheap___redArg,
};
use crate::r#gen::Lean::Server::Snapshots::{
    l_Lean_Server_Snapshots_Snapshot_endPos,
    l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg,
    l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg,
    l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_contains, l_Lean_Syntax_Range_includes, l_Lean_Syntax_Range_overlaps,
    l_Lean_Syntax_getRangeWithTrailing_x3f,
};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_atomically___redArg, l_Std_Mutex_new___redArg,
    runtime_initialize_Std_Sync_Mutex,
};
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_hash, lean_string_utf8_byte_size,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value:
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
    m_fun: l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [1 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instInhabitedRequestError_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Server_instInhabitedRequestError_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instInhabitedRequestError_default___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instInhabitedRequestError_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instInhabitedRequestError_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instInhabitedRequestError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_fileChanged___closed__0_value:
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
        70, 105, 108, 101, 32, 99, 104, 97, 110, 103, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Server_RequestError_fileChanged___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_fileChanged___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_fileChanged___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_RequestError_fileChanged___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_RequestError_fileChanged___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_fileChanged___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_RequestError_fileChanged: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_fileChanged___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_methodNotFound___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        78, 111, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32,
        102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 39, 0,
    ],
};
static mut l_Lean_Server_RequestError_methodNotFound___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_methodNotFound___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_methodNotFound___closed__1_value:
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
    m_data: [39, 0],
};
static mut l_Lean_Server_RequestError_methodNotFound___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_methodNotFound___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_requestCancelled___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_RequestError_requestCancelled___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_requestCancelled___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_RequestError_requestCancelled: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_requestCancelled___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        79, 117, 116, 100, 97, 116, 101, 100, 32, 82, 80, 67, 32, 115, 101, 115, 115, 105, 111,
        110, 0,
    ],
};
static mut l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_RequestError_rpcNeedsReconnect: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_parseRequestParams___redArg___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 114, 101, 113, 117, 101, 115,
        116, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Server_parseRequestParams___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_parseRequestParams___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_parseRequestParams___redArg___closed__1_value:
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
    m_data: [10, 0],
};
static mut l_Lean_Server_parseRequestParams___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_parseRequestParams___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instInhabitedRequestError_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instInhabitedServerRequestResponse___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instMonadLiftIORequestM___closed__0_value:
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
    m_fun: l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instMonadLiftIORequestM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftIORequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instMonadLiftIORequestM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftIORequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value:
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
    m_fun: l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instMonadLiftEIOExceptionRequestM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value:
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
    m_fun: l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instMonadLiftCancellableMRequestM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 115, 101, 114, 118, 101, 114,
        32, 114, 101, 113, 117, 101, 115, 116, 32, 114, 101, 115, 112, 111, 110, 115, 101, 58, 32,
        0,
    ],
};
static mut l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value:
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
        110, 111, 32, 115, 110, 97, 112, 115, 104, 111, 116, 32, 102, 111, 117, 110, 100, 32, 97,
        116, 32, 0,
    ],
};
static mut l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 82, 101, 113, 117, 101, 115, 116,
        115, 0,
    ],
};
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 82, 101, 113, 117, 101, 115, 116,
        77, 46, 102, 105, 110, 100, 67, 109, 100, 68, 97, 116, 97, 65, 116, 80, 111, 115, 0,
    ],
};
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 115, 46, 105, 110, 102, 111, 84, 114, 101, 101, 63, 46, 105, 115, 83, 111, 109,
        101, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0_value:
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
    m_fun: l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value:
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
    m_data: [123, 0],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value:
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
    m_data: [34, 105, 100, 34, 58, 0],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        34, 106, 115, 111, 110, 114, 112, 99, 34, 58, 34, 50, 46, 48, 34, 44, 0,
    ],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value:
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
    m_data: [34, 114, 101, 115, 117, 108, 116, 34, 58, 0],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value:
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
    m_data: [125, 0],
};
static mut l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_requestHandlers: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114,
        32, 102, 111, 114, 32, 39, 0,
    ],
};
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        39, 58, 32, 111, 110, 108, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 100, 117,
        114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110,
        0,
    ],
};
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value:
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
        39, 58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114,
        101, 100, 0,
    ],
};
static mut l_Lean_Server_registerLspRequestHandler___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 111, 114, 105,
        103, 105, 110, 97, 108, 32, 76, 83, 80, 32, 114, 101, 115, 112, 111, 110, 115, 101, 32,
        102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        96, 32, 119, 104, 101, 110, 32, 99, 104, 97, 105, 110, 105, 110, 103, 58, 32, 0,
    ],
};
static mut l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 111, 114, 105,
        103, 105, 110, 97, 108, 32, 76, 83, 80, 32, 114, 101, 115, 112, 111, 110, 115, 101, 32, 74,
        83, 79, 78, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 104, 97, 105, 110, 32, 76, 83, 80, 32,
        114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114,
        32, 39, 0,
    ],
};
static mut l_Lean_Server_chainLspRequestHandler___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        39, 58, 32, 110, 111, 32, 105, 110, 105, 116, 105, 97, 108, 32, 104, 97, 110, 100, 108,
        101, 114, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Server_chainLspRequestHandler___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_statefulRequestHandlers: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [71, 111, 116, 32, 105, 110, 118, 97, 108, 105, 100, 32, 115, 116, 97, 116, 101, 32, 116, 121, 112, 101, 32, 105, 110, 32, 115, 116, 97, 116, 101, 102, 117, 108, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 115, 116, 97, 116, 101, 102, 117, 108, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0]};
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftBaseIOEIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyEIO___aux__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_tryFinally___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<99> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 99,
    m_capacity: 99,
    m_length: 98,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 110, 118, 101, 114, 116, 32, 114,
        101, 115, 112, 111, 110, 115, 101, 32, 111, 102, 32, 112, 114, 101, 118, 105, 111, 117,
        115, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 119,
        104, 101, 110, 32, 99, 104, 97, 105, 110, 105, 110, 103, 32, 115, 116, 97, 116, 101, 102,
        117, 108, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100,
        108, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 97,
    m_capacity: 97,
    m_length: 96,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 114, 101, 115,
        112, 111, 110, 115, 101, 32, 111, 102, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 114,
        101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 119, 104, 101, 110,
        32, 99, 104, 97, 105, 110, 105, 110, 103, 32, 115, 116, 97, 116, 101, 102, 117, 108, 32,
        76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114,
        115, 0,
    ],
};
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 104, 97, 105, 110, 32, 115, 116, 97, 116,
        101, 102, 117, 108, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97,
        110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0,
    ],
};
static mut l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleLspRequest___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [114, 101, 113, 117, 101, 115, 116, 32, 39, 0],
    };
static mut l_Lean_Server_handleLspRequest___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleLspRequest___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleLspRequest___closed__1_value: crate::leanh::LeanStringObject<82> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 82,
        m_capacity: 82,
        m_length: 81,
        m_data: [
            39, 32, 114, 111, 117, 116, 101, 100, 32, 116, 104, 114, 111, 117, 103, 104, 32, 119,
            97, 116, 99, 104, 100, 111, 103, 32, 98, 117, 116, 32, 117, 110, 107, 110, 111, 119,
            110, 32, 105, 110, 32, 119, 111, 114, 107, 101, 114, 59, 32, 97, 114, 101, 32, 98, 111,
            116, 104, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32,
            112, 108, 117, 103, 105, 110, 115, 63, 0,
        ],
    };
static mut l_Lean_Server_handleLspRequest___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleLspRequest___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_FileMap_rangeContainsHoverPos(
    mut v_text_3877_: *mut crate::leanh::LeanObject,
    mut v_r_3878_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_3879_: *mut crate::leanh::LeanObject,
    mut v_includeStop_3880_: u8,
) -> u8 {
    if v_includeStop_3880_ == 0 {
        let mut v_stop_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_source_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isRangeAtEOF_3884_: u8 = 0;
        let mut v___x_3885_: u8 = 0;
        v_stop_3881_ = crate::leanh::lean_ctor_get(v_r_3878_, 1);
        v_source_3882_ = crate::leanh::lean_ctor_get(v_text_3877_, 0);
        v___x_3883_ = lean_string_utf8_byte_size(v_source_3882_);
        v_isRangeAtEOF_3884_ = lean_nat_dec_eq(v_stop_3881_, v___x_3883_);
        v___x_3885_ =
            l_Lean_Syntax_Range_contains(v_r_3878_, v_hoverPos_3879_, v_isRangeAtEOF_3884_);
        return v___x_3885_;
    } else {
        let mut v___x_3886_: u8 = 0;
        v___x_3886_ =
            l_Lean_Syntax_Range_contains(v_r_3878_, v_hoverPos_3879_, v_includeStop_3880_);
        return v___x_3886_;
    }
}
pub unsafe fn l_Lean_FileMap_rangeContainsHoverPos___boxed(
    mut v_text_3887_: *mut crate::leanh::LeanObject,
    mut v_r_3888_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_3889_: *mut crate::leanh::LeanObject,
    mut v_includeStop_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_3891_: u8 = 0;
    let mut v_res_3892_: u8 = 0;
    let mut v_r_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_3891_ = (crate::leanh::lean_unbox(v_includeStop_3890_) as u8);
    v_res_3892_ = l_Lean_FileMap_rangeContainsHoverPos(
        v_text_3887_,
        v_r_3888_,
        v_hoverPos_3889_,
        v_includeStop_boxed_3891_,
    );
    crate::leanh::lean_dec(v_hoverPos_3889_);
    crate::leanh::lean_dec_ref(v_r_3888_);
    crate::leanh::lean_dec_ref(v_text_3887_);
    v_r_3893_ = crate::leanh::lean_box((v_res_3892_) as usize);
    return v_r_3893_;
}
pub unsafe fn l_Lean_FileMap_rangeOverlapsRequestedRange(
    mut v_text_3894_: *mut crate::leanh::LeanObject,
    mut v_documentRange_3895_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3896_: *mut crate::leanh::LeanObject,
    mut v_includeDocumentRangeStop_3897_: u8,
    mut v_includeRequestedRangeStop_3898_: u8,
) -> u8 {
    if v_includeDocumentRangeStop_3897_ == 0 {
        let mut v_stop_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_source_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isDocumentRangeAtEOF_3902_: u8 = 0;
        let mut v___x_3903_: u8 = 0;
        v_stop_3899_ = crate::leanh::lean_ctor_get(v_documentRange_3895_, 1);
        v_source_3900_ = crate::leanh::lean_ctor_get(v_text_3894_, 0);
        v___x_3901_ = lean_string_utf8_byte_size(v_source_3900_);
        v_isDocumentRangeAtEOF_3902_ = lean_nat_dec_eq(v_stop_3899_, v___x_3901_);
        v___x_3903_ = l_Lean_Syntax_Range_overlaps(
            v_documentRange_3895_,
            v_requestedRange_3896_,
            v_isDocumentRangeAtEOF_3902_,
            v_includeRequestedRangeStop_3898_,
        );
        return v___x_3903_;
    } else {
        let mut v___x_3904_: u8 = 0;
        v___x_3904_ = l_Lean_Syntax_Range_overlaps(
            v_documentRange_3895_,
            v_requestedRange_3896_,
            v_includeDocumentRangeStop_3897_,
            v_includeRequestedRangeStop_3898_,
        );
        return v___x_3904_;
    }
}
pub unsafe fn l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(
    mut v_text_3905_: *mut crate::leanh::LeanObject,
    mut v_documentRange_3906_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3907_: *mut crate::leanh::LeanObject,
    mut v_includeDocumentRangeStop_3908_: *mut crate::leanh::LeanObject,
    mut v_includeRequestedRangeStop_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeDocumentRangeStop_boxed_3910_: u8 = 0;
    let mut v_includeRequestedRangeStop_boxed_3911_: u8 = 0;
    let mut v_res_3912_: u8 = 0;
    let mut v_r_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeDocumentRangeStop_boxed_3910_ =
        (crate::leanh::lean_unbox(v_includeDocumentRangeStop_3908_) as u8);
    v_includeRequestedRangeStop_boxed_3911_ =
        (crate::leanh::lean_unbox(v_includeRequestedRangeStop_3909_) as u8);
    v_res_3912_ = l_Lean_FileMap_rangeOverlapsRequestedRange(
        v_text_3905_,
        v_documentRange_3906_,
        v_requestedRange_3907_,
        v_includeDocumentRangeStop_boxed_3910_,
        v_includeRequestedRangeStop_boxed_3911_,
    );
    crate::leanh::lean_dec_ref(v_requestedRange_3907_);
    crate::leanh::lean_dec_ref(v_documentRange_3906_);
    crate::leanh::lean_dec_ref(v_text_3905_);
    v_r_3913_ = crate::leanh::lean_box((v_res_3912_) as usize);
    return v_r_3913_;
}
pub unsafe fn l_Lean_FileMap_rangeIncludesRequestedRange(
    mut v_text_3914_: *mut crate::leanh::LeanObject,
    mut v_documentRange_3915_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3916_: *mut crate::leanh::LeanObject,
    mut v_includeDocumentRangeStop_3917_: u8,
    mut v_includeRequestedRangeStop_3918_: u8,
) -> u8 {
    if v_includeDocumentRangeStop_3917_ == 0 {
        let mut v_stop_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_source_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isDocumentRangeAtEOF_3922_: u8 = 0;
        let mut v___x_3923_: u8 = 0;
        v_stop_3919_ = crate::leanh::lean_ctor_get(v_documentRange_3915_, 1);
        v_source_3920_ = crate::leanh::lean_ctor_get(v_text_3914_, 0);
        v___x_3921_ = lean_string_utf8_byte_size(v_source_3920_);
        v_isDocumentRangeAtEOF_3922_ = lean_nat_dec_eq(v_stop_3919_, v___x_3921_);
        v___x_3923_ = l_Lean_Syntax_Range_includes(
            v_documentRange_3915_,
            v_requestedRange_3916_,
            v_isDocumentRangeAtEOF_3922_,
            v_includeRequestedRangeStop_3918_,
        );
        return v___x_3923_;
    } else {
        let mut v___x_3924_: u8 = 0;
        v___x_3924_ = l_Lean_Syntax_Range_includes(
            v_documentRange_3915_,
            v_requestedRange_3916_,
            v_includeDocumentRangeStop_3917_,
            v_includeRequestedRangeStop_3918_,
        );
        return v___x_3924_;
    }
}
pub unsafe fn l_Lean_FileMap_rangeIncludesRequestedRange___boxed(
    mut v_text_3925_: *mut crate::leanh::LeanObject,
    mut v_documentRange_3926_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_3927_: *mut crate::leanh::LeanObject,
    mut v_includeDocumentRangeStop_3928_: *mut crate::leanh::LeanObject,
    mut v_includeRequestedRangeStop_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeDocumentRangeStop_boxed_3930_: u8 = 0;
    let mut v_includeRequestedRangeStop_boxed_3931_: u8 = 0;
    let mut v_res_3932_: u8 = 0;
    let mut v_r_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeDocumentRangeStop_boxed_3930_ =
        (crate::leanh::lean_unbox(v_includeDocumentRangeStop_3928_) as u8);
    v_includeRequestedRangeStop_boxed_3931_ =
        (crate::leanh::lean_unbox(v_includeRequestedRangeStop_3929_) as u8);
    v_res_3932_ = l_Lean_FileMap_rangeIncludesRequestedRange(
        v_text_3925_,
        v_documentRange_3926_,
        v_requestedRange_3927_,
        v_includeDocumentRangeStop_boxed_3930_,
        v_includeRequestedRangeStop_boxed_3931_,
    );
    crate::leanh::lean_dec_ref(v_requestedRange_3927_);
    crate::leanh::lean_dec_ref(v_documentRange_3926_);
    crate::leanh::lean_dec_ref(v_text_3925_);
    v_r_3933_ = crate::leanh::lean_box((v_res_3932_) as usize);
    return v_r_3933_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(
    mut v_x_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3934_) == 0 {
        let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3935_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3935_;
    } else {
        let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3936_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3936_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(
    mut v_x_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3938_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(v_x_3937_);
    crate::leanh::lean_dec(v_x_3937_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(
    mut v_t_3939_: *mut crate::leanh::LeanObject,
    mut v_k_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3939_) == 0 {
        return v_k_3940_;
    } else {
        let mut v_foldChildren_3941_: u8 = 0;
        let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_foldChildren_3941_ = crate::leanh::lean_ctor_get_uint8(v_t_3939_, 0 as u32);
        v___x_3942_ = crate::leanh::lean_box((v_foldChildren_3941_) as usize);
        v___x_3943_ = crate::leanh::lean_apply_1(v_k_3940_, v___x_3942_);
        return v___x_3943_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(
    mut v_t_3944_: *mut crate::leanh::LeanObject,
    mut v_k_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ =
        l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_3944_, v_k_3945_);
    crate::leanh::lean_dec(v_t_3944_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(
    mut v_motive_3947_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3948_: *mut crate::leanh::LeanObject,
    mut v_t_3949_: *mut crate::leanh::LeanObject,
    mut v_h_3950_: *mut crate::leanh::LeanObject,
    mut v_k_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ =
        l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_3949_, v_k_3951_);
    return v___x_3952_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(
    mut v_motive_3953_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3954_: *mut crate::leanh::LeanObject,
    mut v_t_3955_: *mut crate::leanh::LeanObject,
    mut v_h_3956_: *mut crate::leanh::LeanObject,
    mut v_k_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(
        v_motive_3953_,
        v_ctorIdx_3954_,
        v_t_3955_,
        v_h_3956_,
        v_k_3957_,
    );
    crate::leanh::lean_dec(v_t_3955_);
    crate::leanh::lean_dec(v_ctorIdx_3954_);
    return v_res_3958_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(
    mut v_t_3959_: *mut crate::leanh::LeanObject,
    mut v_done_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ =
        l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_3959_, v_done_3960_);
    return v___x_3961_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(
    mut v_t_3962_: *mut crate::leanh::LeanObject,
    mut v_done_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ =
        l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(v_t_3962_, v_done_3963_);
    crate::leanh::lean_dec(v_t_3962_);
    return v_res_3964_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(
    mut v_motive_3965_: *mut crate::leanh::LeanObject,
    mut v_t_3966_: *mut crate::leanh::LeanObject,
    mut v_h_3967_: *mut crate::leanh::LeanObject,
    mut v_done_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3969_ =
        l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_3966_, v_done_3968_);
    return v___x_3969_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(
    mut v_motive_3970_: *mut crate::leanh::LeanObject,
    mut v_t_3971_: *mut crate::leanh::LeanObject,
    mut v_h_3972_: *mut crate::leanh::LeanObject,
    mut v_done_3973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(
        v_motive_3970_,
        v_t_3971_,
        v_h_3972_,
        v_done_3973_,
    );
    crate::leanh::lean_dec(v_t_3971_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(
    mut v_t_3975_: *mut crate::leanh::LeanObject,
    mut v_proceed_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(
        v_t_3975_,
        v_proceed_3976_,
    );
    return v___x_3977_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(
    mut v_t_3978_: *mut crate::leanh::LeanObject,
    mut v_proceed_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3980_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(
        v_t_3978_,
        v_proceed_3979_,
    );
    crate::leanh::lean_dec(v_t_3978_);
    return v_res_3980_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(
    mut v_motive_3981_: *mut crate::leanh::LeanObject,
    mut v_t_3982_: *mut crate::leanh::LeanObject,
    mut v_h_3983_: *mut crate::leanh::LeanObject,
    mut v_proceed_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(
        v_t_3982_,
        v_proceed_3984_,
    );
    return v___x_3985_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(
    mut v_motive_3986_: *mut crate::leanh::LeanObject,
    mut v_t_3987_: *mut crate::leanh::LeanObject,
    mut v_h_3988_: *mut crate::leanh::LeanObject,
    mut v_proceed_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(
        v_motive_3986_,
        v_t_3987_,
        v_h_3988_,
        v_proceed_3989_,
    );
    crate::leanh::lean_dec(v_t_3987_);
    return v_res_3990_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(
    mut v_f_3991_: *mut crate::leanh::LeanObject,
    mut v_tail_3992_: *mut crate::leanh::LeanObject,
    mut v_x_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    v_snd_3994_ = crate::leanh::lean_ctor_get(v_x_3993_, 1);
    v___x_3995_ = (crate::leanh::lean_unbox(v_snd_3994_) as u8);
    if v___x_3995_ == 0 {
        let mut v_fst_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fst_3996_ = crate::leanh::lean_ctor_get(v_x_3993_, 0);
        crate::leanh::lean_inc(v_fst_3996_);
        crate::leanh::lean_dec_ref(v_x_3993_);
        v___x_3997_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_3991_, v_fst_3996_, v_tail_3992_);
        return v___x_3997_;
    } else {
        let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_3992_);
        crate::leanh::lean_dec_ref(v_f_3991_);
        v___x_3998_ = lean_task_pure(v_x_3993_);
        return v___x_3998_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(
    mut v_f_3999_: *mut crate::leanh::LeanObject,
    mut v_tail_4000_: *mut crate::leanh::LeanObject,
    mut v_head_4001_: *mut crate::leanh::LeanObject,
    mut v___f_4002_: *mut crate::leanh::LeanObject,
    mut v_x_4003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foldChildren_4005_: u8 = 0;
    let mut v_fst_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subtreeTask_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut v_unused_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4004_ = crate::leanh::lean_ctor_get(v_x_4003_, 1);
                if crate::leanh::lean_obj_tag(v_snd_4004_) == 1 {
                    v_foldChildren_4005_ = crate::leanh::lean_ctor_get_uint8(v_snd_4004_, 0 as u32);
                    if v_foldChildren_4005_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_4002_);
                        crate::leanh::lean_dec_ref(v_head_4001_);
                        v_fst_4006_ = crate::leanh::lean_ctor_get(v_x_4003_, 0);
                        crate::leanh::lean_inc(v_fst_4006_);
                        crate::leanh::lean_dec_ref(v_x_4003_);
                        v___x_4007_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_3999_, v_fst_4006_, v_tail_4000_);
                        return v___x_4007_;
                    } else {
                        crate::leanh::lean_dec(v_tail_4000_);
                        v_fst_4008_ = crate::leanh::lean_ctor_get(v_x_4003_, 0);
                        crate::leanh::lean_inc(v_fst_4008_);
                        crate::leanh::lean_dec_ref(v_x_4003_);
                        v_task_4009_ = crate::leanh::lean_ctor_get(v_head_4001_, 3);
                        crate::leanh::lean_inc_ref(v_task_4009_);
                        crate::leanh::lean_dec_ref(v_head_4001_);
                        v___f_4010_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_4010_, 0, v_f_3999_);
                        crate::leanh::lean_closure_set(v___f_4010_, 1, v_fst_4008_);
                        v_subtreeTask_4011_ =
                            l_Lean_Server_ServerTask_bindCheap___redArg(v_task_4009_, v___f_4010_);
                        v___x_4012_ = l_Lean_Server_ServerTask_bindCheap___redArg(
                            v_subtreeTask_4011_,
                            v___f_4002_,
                        );
                        return v___x_4012_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_4002_);
                    crate::leanh::lean_dec_ref(v_head_4001_);
                    crate::leanh::lean_dec(v_tail_4000_);
                    crate::leanh::lean_dec_ref(v_f_3999_);
                    v_fst_4013_ = crate::leanh::lean_ctor_get(v_x_4003_, 0);
                    v_isSharedCheck_4023_ = (!crate::leanh::lean_is_exclusive(v_x_4003_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v_unused_4024_ = crate::leanh::lean_ctor_get(v_x_4003_, 1);
                        crate::leanh::lean_dec(v_unused_4024_);
                        v___x_4015_ = v_x_4003_;
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4013_);
                        crate::leanh::lean_dec(v_x_4003_);
                        v___x_4015_ = crate::leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4017_ = 1;
                v___x_4018_ = crate::leanh::lean_box((v___x_4017_) as usize);
                if v_isShared_4016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4015_, 1, v___x_4018_);
                    v___x_4020_ = v___x_4015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4021_ = lean_task_pure(v___x_4020_);
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(
    mut v_f_4025_: *mut crate::leanh::LeanObject,
    mut v_acc_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_4027_) == 0 {
        let mut v___x_4028_: u8 = 0;
        let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_4025_);
        v___x_4028_ = 0;
        v___x_4029_ = crate::leanh::lean_box((v___x_4028_) as usize);
        v___x_4030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4030_, 0, v_acc_4026_);
        crate::leanh::lean_ctor_set(v___x_4030_, 1, v___x_4029_);
        v___x_4031_ = lean_task_pure(v___x_4030_);
        return v___x_4031_;
    } else {
        let mut v_head_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_4032_ = crate::leanh::lean_ctor_get(v_a_4027_, 0);
        crate::leanh::lean_inc_n(v_head_4032_, 2);
        v_tail_4033_ = crate::leanh::lean_ctor_get(v_a_4027_, 1);
        crate::leanh::lean_inc_n(v_tail_4033_, 2);
        crate::leanh::lean_dec_ref_known(v_a_4027_, 2);
        crate::leanh::lean_inc_ref_n(v_f_4025_, 2);
        v___f_4034_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_4034_, 0, v_f_4025_);
        crate::leanh::lean_closure_set(v___f_4034_, 1, v_tail_4033_);
        v___f_4035_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_4035_, 0, v_f_4025_);
        crate::leanh::lean_closure_set(v___f_4035_, 1, v_tail_4033_);
        crate::leanh::lean_closure_set(v___f_4035_, 2, v_head_4032_);
        crate::leanh::lean_closure_set(v___f_4035_, 3, v___f_4034_);
        v___x_4036_ = crate::leanh::lean_apply_2(v_f_4025_, v_head_4032_, v_acc_4026_);
        v___x_4037_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_4036_, v___f_4035_);
        return v___x_4037_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(
    mut v_f_4038_: *mut crate::leanh::LeanObject,
    mut v_acc_4039_: *mut crate::leanh::LeanObject,
    mut v_tree_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_children_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_children_4041_ = crate::leanh::lean_ctor_get(v_tree_4040_, 1);
    crate::leanh::lean_inc_ref(v_children_4041_);
    crate::leanh::lean_dec_ref(v_tree_4040_);
    v___x_4042_ = lean_array_to_list(v_children_4041_);
    v___x_4043_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_4038_, v_acc_4039_, v___x_4042_);
    return v___x_4043_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(
    mut v_f_4044_: *mut crate::leanh::LeanObject,
    mut v_fst_4045_: *mut crate::leanh::LeanObject,
    mut v_tree_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_4044_, v_fst_4045_, v_tree_4046_);
    return v___x_4047_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(
    mut v_00_u03b1_4048_: *mut crate::leanh::LeanObject,
    mut v_f_4049_: *mut crate::leanh::LeanObject,
    mut v_acc_4050_: *mut crate::leanh::LeanObject,
    mut v_tree_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_4049_, v_acc_4050_, v_tree_4051_);
    return v___x_4052_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(
    mut v_00_u03b1_4053_: *mut crate::leanh::LeanObject,
    mut v_f_4054_: *mut crate::leanh::LeanObject,
    mut v_acc_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_4054_, v_acc_4055_, v_a_4056_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(
    mut v_x_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4059_ = crate::leanh::lean_ctor_get(v_x_4058_, 0);
    crate::leanh::lean_inc(v_fst_4059_);
    return v_fst_4059_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(
    mut v_x_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(v_x_4060_);
    crate::leanh::lean_dec_ref(v_x_4060_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps___redArg(
    mut v_tree_4063_: *mut crate::leanh::LeanObject,
    mut v_init_4064_: *mut crate::leanh::LeanObject,
    mut v_f_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4066_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0;
    v_t_4067_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_4065_, v_init_4064_, v_tree_4063_);
    v___x_4068_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4066_, v_t_4067_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldSnaps(
    mut v_00_u03b1_4069_: *mut crate::leanh::LeanObject,
    mut v_tree_4070_: *mut crate::leanh::LeanObject,
    mut v_init_4071_: *mut crate::leanh::LeanObject,
    mut v_f_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4073_ =
        l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_4070_, v_init_4071_, v_f_4072_);
    return v___x_4073_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(
    mut v___x_4074_: u8,
    mut v___x_4075_: *mut crate::leanh::LeanObject,
    mut v_tree_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_element_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v_infoTree_x3f_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_unused_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_element_4077_ = crate::leanh::lean_ctor_get(v_tree_4076_, 0);
                v_isSharedCheck_4090_ = (!crate::leanh::lean_is_exclusive(v_tree_4076_)) as u8;
                if v_isSharedCheck_4090_ == 0 {
                    v_unused_4091_ = crate::leanh::lean_ctor_get(v_tree_4076_, 1);
                    crate::leanh::lean_dec(v_unused_4091_);
                    v___x_4079_ = v_tree_4076_;
                    v_isShared_4080_ = v_isSharedCheck_4090_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_element_4077_);
                    crate::leanh::lean_dec(v_tree_4076_);
                    v___x_4079_ = crate::leanh::lean_box(0);
                    v_isShared_4080_ = v_isSharedCheck_4090_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_infoTree_x3f_4081_ = crate::leanh::lean_ctor_get(v_element_4077_, 2);
                crate::leanh::lean_inc(v_infoTree_x3f_4081_);
                crate::leanh::lean_dec_ref(v_element_4077_);
                if crate::leanh::lean_obj_tag(v_infoTree_x3f_4081_) == 1 {
                    crate::leanh::lean_dec(v___x_4075_);
                    v___x_4082_ = crate::leanh::lean_box(0);
                    if v_isShared_4080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4079_, 1, v___x_4082_);
                        crate::leanh::lean_ctor_set(v___x_4079_, 0, v_infoTree_x3f_4081_);
                        v___x_4084_ = v___x_4079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4085_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_4085_,
                            0,
                            v_infoTree_x3f_4081_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 1, v___x_4082_);
                        v___x_4084_ = v_reuseFailAlloc_4085_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_infoTree_x3f_4081_);
                    v___x_4086_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_4086_, 0 as u32, v___x_4074_);
                    if v_isShared_4080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4079_, 1, v___x_4086_);
                        crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4075_);
                        v___x_4088_ = v___x_4079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4086_);
                        v___x_4088_ = v_reuseFailAlloc_4089_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4084_;
            }
            3 => {
                return v___x_4088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(
    mut v___x_4092_: *mut crate::leanh::LeanObject,
    mut v___x_4093_: *mut crate::leanh::LeanObject,
    mut v_tree_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_469__boxed_4095_: u8 = 0;
    let mut v_res_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469__boxed_4095_ = (crate::leanh::lean_unbox(v___x_4092_) as u8);
    v_res_4096_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(
        v___x_469__boxed_4095_,
        v___x_4093_,
        v_tree_4094_,
    );
    return v_res_4096_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(
    mut v_text_4101_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_4102_: *mut crate::leanh::LeanObject,
    mut v_includeStop_4103_: u8,
    mut v___x_4104_: *mut crate::leanh::LeanObject,
    mut v_snap_4105_: *mut crate::leanh::LeanObject,
    mut v_x_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_x3f_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stx_x3f_4107_ = crate::leanh::lean_ctor_get(v_snap_4105_, 0);
    crate::leanh::lean_inc(v_stx_x3f_4107_);
    if crate::leanh::lean_obj_tag(v_stx_x3f_4107_) == 1 {
        let mut v_task_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4110_: u8 = 0;
        let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_task_4108_ = crate::leanh::lean_ctor_get(v_snap_4105_, 3);
        crate::leanh::lean_inc_ref(v_task_4108_);
        crate::leanh::lean_dec_ref(v_snap_4105_);
        v_val_4109_ = crate::leanh::lean_ctor_get(v_stx_x3f_4107_, 0);
        crate::leanh::lean_inc(v_val_4109_);
        crate::leanh::lean_dec_ref_known(v_stx_x3f_4107_, 1);
        v___x_4110_ = 1;
        v___x_4111_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_4109_, v___x_4110_);
        crate::leanh::lean_dec(v_val_4109_);
        if crate::leanh::lean_obj_tag(v___x_4111_) == 1 {
            let mut v_val_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4113_: u8 = 0;
            v_val_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
            crate::leanh::lean_inc(v_val_4112_);
            crate::leanh::lean_dec_ref_known(v___x_4111_, 1);
            v___x_4113_ = l_Lean_FileMap_rangeContainsHoverPos(
                v_text_4101_,
                v_val_4112_,
                v_hoverPos_4102_,
                v_includeStop_4103_,
            );
            crate::leanh::lean_dec(v_val_4112_);
            if v___x_4113_ == 0 {
                let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_task_4108_);
                v___x_4114_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4114_, 0 as u32, v___x_4113_);
                v___x_4115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4115_, 0, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4114_);
                v___x_4116_ = lean_task_pure(v___x_4115_);
                return v___x_4116_;
            } else {
                let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4117_ = crate::leanh::lean_box((v___x_4113_) as usize);
                v___f_4118_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4118_, 0, v___x_4117_);
                crate::leanh::lean_closure_set(v___f_4118_, 1, v___x_4104_);
                v___x_4119_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4118_, v_task_4108_);
                return v___x_4119_;
            }
        } else {
            let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4111_);
            crate::leanh::lean_dec_ref(v_task_4108_);
            v___x_4120_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0;
            v___x_4121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4121_, 0, v___x_4104_);
            crate::leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
            v___x_4122_ = lean_task_pure(v___x_4121_);
            return v___x_4122_;
        }
    } else {
        let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_x3f_4107_);
        crate::leanh::lean_dec_ref(v_snap_4105_);
        v___x_4123_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1;
        v___x_4124_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4104_);
        crate::leanh::lean_ctor_set(v___x_4124_, 1, v___x_4123_);
        v___x_4125_ = lean_task_pure(v___x_4124_);
        return v___x_4125_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(
    mut v_text_4126_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_4127_: *mut crate::leanh::LeanObject,
    mut v_includeStop_4128_: *mut crate::leanh::LeanObject,
    mut v___x_4129_: *mut crate::leanh::LeanObject,
    mut v_snap_4130_: *mut crate::leanh::LeanObject,
    mut v_x_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_4132_: u8 = 0;
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_4132_ = (crate::leanh::lean_unbox(v_includeStop_4128_) as u8);
    v_res_4133_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(
        v_text_4126_,
        v_hoverPos_4127_,
        v_includeStop_boxed_4132_,
        v___x_4129_,
        v_snap_4130_,
        v_x_4131_,
    );
    crate::leanh::lean_dec(v_x_4131_);
    crate::leanh::lean_dec(v_hoverPos_4127_);
    crate::leanh::lean_dec_ref(v_text_4126_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos(
    mut v_text_4134_: *mut crate::leanh::LeanObject,
    mut v_tree_4135_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_4136_: *mut crate::leanh::LeanObject,
    mut v_includeStop_4137_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = crate::leanh::lean_box(0);
    v___x_4139_ = crate::leanh::lean_box((v_includeStop_4137_) as usize);
    v___f_4140_ = crate::leanh::lean_alloc_closure(
        l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4140_, 0, v_text_4134_);
    crate::leanh::lean_closure_set(v___f_4140_, 1, v_hoverPos_4136_);
    crate::leanh::lean_closure_set(v___f_4140_, 2, v___x_4139_);
    crate::leanh::lean_closure_set(v___f_4140_, 3, v___x_4138_);
    v___x_4141_ =
        l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_4135_, v___x_4138_, v___f_4140_);
    return v___x_4141_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(
    mut v_text_4142_: *mut crate::leanh::LeanObject,
    mut v_tree_4143_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_4144_: *mut crate::leanh::LeanObject,
    mut v_includeStop_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_4146_: u8 = 0;
    let mut v_res_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_4146_ = (crate::leanh::lean_unbox(v_includeStop_4145_) as u8);
    v_res_4147_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(
        v_text_4142_,
        v_tree_4143_,
        v_hoverPos_4144_,
        v_includeStop_boxed_4146_,
    );
    return v_res_4147_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(
    mut v_requestedRange_4148_: *mut crate::leanh::LeanObject,
    mut v___x_4149_: u8,
    mut v_f_4150_: *mut crate::leanh::LeanObject,
    mut v_ctx_4151_: *mut crate::leanh::LeanObject,
    mut v_i_4152_: *mut crate::leanh::LeanObject,
    mut v_acc_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_Elab_Info_range_x3f(v_i_4152_);
    if crate::leanh::lean_obj_tag(v___x_4154_) == 1 {
        let mut v_val_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: u8 = 0;
        v_val_4155_ = crate::leanh::lean_ctor_get(v___x_4154_, 0);
        crate::leanh::lean_inc(v_val_4155_);
        crate::leanh::lean_dec_ref_known(v___x_4154_, 1);
        v___x_4156_ = l_Lean_Syntax_Range_overlaps(
            v_val_4155_,
            v_requestedRange_4148_,
            v___x_4149_,
            v___x_4149_,
        );
        crate::leanh::lean_dec(v_val_4155_);
        if v___x_4156_ == 0 {
            crate::leanh::lean_dec_ref(v_i_4152_);
            crate::leanh::lean_dec_ref(v_ctx_4151_);
            crate::leanh::lean_dec(v_f_4150_);
            return v_acc_4153_;
        } else {
            let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4157_ =
                crate::leanh::lean_apply_3(v_f_4150_, v_ctx_4151_, v_i_4152_, v_acc_4153_);
            return v___x_4157_;
        }
    } else {
        crate::leanh::lean_dec(v___x_4154_);
        crate::leanh::lean_dec_ref(v_i_4152_);
        crate::leanh::lean_dec_ref(v_ctx_4151_);
        crate::leanh::lean_dec(v_f_4150_);
        return v_acc_4153_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(
    mut v_requestedRange_4158_: *mut crate::leanh::LeanObject,
    mut v___x_4159_: *mut crate::leanh::LeanObject,
    mut v_f_4160_: *mut crate::leanh::LeanObject,
    mut v_ctx_4161_: *mut crate::leanh::LeanObject,
    mut v_i_4162_: *mut crate::leanh::LeanObject,
    mut v_acc_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631__boxed_4164_: u8 = 0;
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631__boxed_4164_ = (crate::leanh::lean_unbox(v___x_4159_) as u8);
    v_res_4165_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(
        v_requestedRange_4158_,
        v___x_631__boxed_4164_,
        v_f_4160_,
        v_ctx_4161_,
        v_i_4162_,
        v_acc_4163_,
    );
    crate::leanh::lean_dec_ref(v_requestedRange_4158_);
    return v_res_4165_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(
    mut v___f_4166_: *mut crate::leanh::LeanObject,
    mut v_acc_4167_: *mut crate::leanh::LeanObject,
    mut v___x_4168_: u8,
    mut v_tree_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_element_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4173_: u8 = 0;
    let mut v_infoTree_x3f_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_unused_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_element_4170_ = crate::leanh::lean_ctor_get(v_tree_4169_, 0);
                v_isSharedCheck_4185_ = (!crate::leanh::lean_is_exclusive(v_tree_4169_)) as u8;
                if v_isSharedCheck_4185_ == 0 {
                    v_unused_4186_ = crate::leanh::lean_ctor_get(v_tree_4169_, 1);
                    crate::leanh::lean_dec(v_unused_4186_);
                    v___x_4172_ = v_tree_4169_;
                    v_isShared_4173_ = v_isSharedCheck_4185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_element_4170_);
                    crate::leanh::lean_dec(v_tree_4169_);
                    v___x_4172_ = crate::leanh::lean_box(0);
                    v_isShared_4173_ = v_isSharedCheck_4185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_infoTree_x3f_4174_ = crate::leanh::lean_ctor_get(v_element_4170_, 2);
                crate::leanh::lean_inc(v_infoTree_x3f_4174_);
                crate::leanh::lean_dec_ref(v_element_4170_);
                if crate::leanh::lean_obj_tag(v_infoTree_x3f_4174_) == 1 {
                    v_val_4175_ = crate::leanh::lean_ctor_get(v_infoTree_x3f_4174_, 0);
                    crate::leanh::lean_inc(v_val_4175_);
                    crate::leanh::lean_dec_ref_known(v_infoTree_x3f_4174_, 1);
                    v_acc_4176_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                        v___f_4166_,
                        v_acc_4167_,
                        v_val_4175_,
                    );
                    v___x_4177_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_4177_, 0 as u32, v___x_4168_);
                    if v_isShared_4173_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4172_, 1, v___x_4177_);
                        crate::leanh::lean_ctor_set(v___x_4172_, 0, v_acc_4176_);
                        v___x_4179_ = v___x_4172_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_acc_4176_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4177_);
                        v___x_4179_ = v_reuseFailAlloc_4180_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_infoTree_x3f_4174_);
                    crate::leanh::lean_dec(v___f_4166_);
                    v___x_4181_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_4181_, 0 as u32, v___x_4168_);
                    if v_isShared_4173_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4172_, 1, v___x_4181_);
                        crate::leanh::lean_ctor_set(v___x_4172_, 0, v_acc_4167_);
                        v___x_4183_ = v___x_4172_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_acc_4167_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___x_4181_);
                        v___x_4183_ = v_reuseFailAlloc_4184_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4179_;
            }
            3 => {
                return v___x_4183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(
    mut v___f_4187_: *mut crate::leanh::LeanObject,
    mut v_acc_4188_: *mut crate::leanh::LeanObject,
    mut v___x_4189_: *mut crate::leanh::LeanObject,
    mut v_tree_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643__boxed_4191_: u8 = 0;
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643__boxed_4191_ = (crate::leanh::lean_unbox(v___x_4189_) as u8);
    v_res_4192_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(
        v___f_4187_,
        v_acc_4188_,
        v___x_643__boxed_4191_,
        v_tree_4190_,
    );
    return v_res_4192_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(
    mut v_requestedRange_4193_: *mut crate::leanh::LeanObject,
    mut v_f_4194_: *mut crate::leanh::LeanObject,
    mut v_snap_4195_: *mut crate::leanh::LeanObject,
    mut v_acc_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_x3f_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stx_x3f_4197_ = crate::leanh::lean_ctor_get(v_snap_4195_, 0);
    crate::leanh::lean_inc(v_stx_x3f_4197_);
    if crate::leanh::lean_obj_tag(v_stx_x3f_4197_) == 1 {
        let mut v_task_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4200_: u8 = 0;
        let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_task_4198_ = crate::leanh::lean_ctor_get(v_snap_4195_, 3);
        crate::leanh::lean_inc_ref(v_task_4198_);
        crate::leanh::lean_dec_ref(v_snap_4195_);
        v_val_4199_ = crate::leanh::lean_ctor_get(v_stx_x3f_4197_, 0);
        crate::leanh::lean_inc(v_val_4199_);
        crate::leanh::lean_dec_ref_known(v_stx_x3f_4197_, 1);
        v___x_4200_ = 1;
        v___x_4201_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_4199_, v___x_4200_);
        crate::leanh::lean_dec(v_val_4199_);
        if crate::leanh::lean_obj_tag(v___x_4201_) == 1 {
            let mut v_val_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4203_: u8 = 0;
            v_val_4202_ = crate::leanh::lean_ctor_get(v___x_4201_, 0);
            crate::leanh::lean_inc(v_val_4202_);
            crate::leanh::lean_dec_ref_known(v___x_4201_, 1);
            v___x_4203_ = l_Lean_Syntax_Range_overlaps(
                v_val_4202_,
                v_requestedRange_4193_,
                v___x_4200_,
                v___x_4200_,
            );
            crate::leanh::lean_dec(v_val_4202_);
            if v___x_4203_ == 0 {
                let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_task_4198_);
                crate::leanh::lean_dec(v_f_4194_);
                crate::leanh::lean_dec_ref(v_requestedRange_4193_);
                v___x_4204_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4204_, 0 as u32, v___x_4203_);
                v___x_4205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4205_, 0, v_acc_4196_);
                crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4204_);
                v___x_4206_ = lean_task_pure(v___x_4205_);
                return v___x_4206_;
            } else {
                let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4207_ = crate::leanh::lean_box((v___x_4200_) as usize);
                v___f_4208_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4208_, 0, v_requestedRange_4193_);
                crate::leanh::lean_closure_set(v___f_4208_, 1, v___x_4207_);
                crate::leanh::lean_closure_set(v___f_4208_, 2, v_f_4194_);
                v___x_4209_ = crate::leanh::lean_box((v___x_4200_) as usize);
                v___f_4210_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4210_, 0, v___f_4208_);
                crate::leanh::lean_closure_set(v___f_4210_, 1, v_acc_4196_);
                crate::leanh::lean_closure_set(v___f_4210_, 2, v___x_4209_);
                v___x_4211_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4210_, v_task_4198_);
                return v___x_4211_;
            }
        } else {
            let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4201_);
            crate::leanh::lean_dec_ref(v_task_4198_);
            crate::leanh::lean_dec(v_f_4194_);
            crate::leanh::lean_dec_ref(v_requestedRange_4193_);
            v___x_4212_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0;
            v___x_4213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4213_, 0, v_acc_4196_);
            crate::leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
            v___x_4214_ = lean_task_pure(v___x_4213_);
            return v___x_4214_;
        }
    } else {
        let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_x3f_4197_);
        crate::leanh::lean_dec_ref(v_snap_4195_);
        crate::leanh::lean_dec(v_f_4194_);
        crate::leanh::lean_dec_ref(v_requestedRange_4193_);
        v___x_4215_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1;
        v___x_4216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4216_, 0, v_acc_4196_);
        crate::leanh::lean_ctor_set(v___x_4216_, 1, v___x_4215_);
        v___x_4217_ = lean_task_pure(v___x_4216_);
        return v___x_4217_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(
    mut v_tree_4218_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_4219_: *mut crate::leanh::LeanObject,
    mut v_init_4220_: *mut crate::leanh::LeanObject,
    mut v_f_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4222_ = crate::leanh::lean_alloc_closure(
        l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4222_, 0, v_requestedRange_4219_);
    crate::leanh::lean_closure_set(v___f_4222_, 1, v_f_4221_);
    v___x_4223_ =
        l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_4218_, v_init_4220_, v___f_4222_);
    return v___x_4223_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldInfosInRange(
    mut v_00_u03b1_4224_: *mut crate::leanh::LeanObject,
    mut v_tree_4225_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_4226_: *mut crate::leanh::LeanObject,
    mut v_init_4227_: *mut crate::leanh::LeanObject,
    mut v_f_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4229_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(
        v_tree_4225_,
        v_requestedRange_4226_,
        v_init_4227_,
        v_f_4228_,
    );
    return v___x_4229_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(
    mut v_log_4230_: *mut crate::leanh::LeanObject,
    mut v___x_4231_: u8,
    mut v_tree_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_element_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_unused_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_element_4233_ = crate::leanh::lean_ctor_get(v_tree_4232_, 0);
                crate::leanh::lean_inc_ref(v_element_4233_);
                crate::leanh::lean_dec_ref(v_tree_4232_);
                v_diagnostics_4234_ = crate::leanh::lean_ctor_get(v_element_4233_, 1);
                crate::leanh::lean_inc_ref(v_diagnostics_4234_);
                crate::leanh::lean_dec_ref(v_element_4233_);
                v_msgLog_4235_ = crate::leanh::lean_ctor_get(v_diagnostics_4234_, 0);
                v_isSharedCheck_4244_ =
                    (!crate::leanh::lean_is_exclusive(v_diagnostics_4234_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v_unused_4245_ = crate::leanh::lean_ctor_get(v_diagnostics_4234_, 1);
                    crate::leanh::lean_dec(v_unused_4245_);
                    v___x_4237_ = v_diagnostics_4234_;
                    v_isShared_4238_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_msgLog_4235_);
                    crate::leanh::lean_dec(v_diagnostics_4234_);
                    v___x_4237_ = crate::leanh::lean_box(0);
                    v_isShared_4238_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4239_ = l_Lean_MessageLog_append(v_log_4230_, v_msgLog_4235_);
                v___x_4240_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4240_, 0 as u32, v___x_4231_);
                if v_isShared_4238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4237_, 1, v___x_4240_);
                    crate::leanh::lean_ctor_set(v___x_4237_, 0, v___x_4239_);
                    v___x_4242_ = v___x_4237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___x_4240_);
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(
    mut v_log_4246_: *mut crate::leanh::LeanObject,
    mut v___x_4247_: *mut crate::leanh::LeanObject,
    mut v_tree_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422__boxed_4249_: u8 = 0;
    let mut v_res_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422__boxed_4249_ = (crate::leanh::lean_unbox(v___x_4247_) as u8);
    v_res_4250_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(
        v_log_4246_,
        v___x_422__boxed_4249_,
        v_tree_4248_,
    );
    return v_res_4250_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(
    mut v_requestedRange_4251_: *mut crate::leanh::LeanObject,
    mut v_snap_4252_: *mut crate::leanh::LeanObject,
    mut v_log_4253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_x3f_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stx_x3f_4254_ = crate::leanh::lean_ctor_get(v_snap_4252_, 0);
    crate::leanh::lean_inc(v_stx_x3f_4254_);
    if crate::leanh::lean_obj_tag(v_stx_x3f_4254_) == 1 {
        let mut v_task_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4257_: u8 = 0;
        let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_task_4255_ = crate::leanh::lean_ctor_get(v_snap_4252_, 3);
        crate::leanh::lean_inc_ref(v_task_4255_);
        crate::leanh::lean_dec_ref(v_snap_4252_);
        v_val_4256_ = crate::leanh::lean_ctor_get(v_stx_x3f_4254_, 0);
        crate::leanh::lean_inc(v_val_4256_);
        crate::leanh::lean_dec_ref_known(v_stx_x3f_4254_, 1);
        v___x_4257_ = 1;
        v___x_4258_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_4256_, v___x_4257_);
        crate::leanh::lean_dec(v_val_4256_);
        if crate::leanh::lean_obj_tag(v___x_4258_) == 1 {
            let mut v_val_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4260_: u8 = 0;
            v_val_4259_ = crate::leanh::lean_ctor_get(v___x_4258_, 0);
            crate::leanh::lean_inc(v_val_4259_);
            crate::leanh::lean_dec_ref_known(v___x_4258_, 1);
            v___x_4260_ = l_Lean_Syntax_Range_overlaps(
                v_val_4259_,
                v_requestedRange_4251_,
                v___x_4257_,
                v___x_4257_,
            );
            crate::leanh::lean_dec(v_val_4259_);
            if v___x_4260_ == 0 {
                let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_task_4255_);
                v___x_4261_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4261_, 0 as u32, v___x_4260_);
                v___x_4262_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4262_, 0, v_log_4253_);
                crate::leanh::lean_ctor_set(v___x_4262_, 1, v___x_4261_);
                v___x_4263_ = lean_task_pure(v___x_4262_);
                return v___x_4263_;
            } else {
                let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4264_ = crate::leanh::lean_box((v___x_4257_) as usize);
                v___f_4265_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4265_, 0, v_log_4253_);
                crate::leanh::lean_closure_set(v___f_4265_, 1, v___x_4264_);
                v___x_4266_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4265_, v_task_4255_);
                return v___x_4266_;
            }
        } else {
            let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4258_);
            crate::leanh::lean_dec_ref(v_task_4255_);
            v___x_4267_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0;
            v___x_4268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4268_, 0, v_log_4253_);
            crate::leanh::lean_ctor_set(v___x_4268_, 1, v___x_4267_);
            v___x_4269_ = lean_task_pure(v___x_4268_);
            return v___x_4269_;
        }
    } else {
        let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_x3f_4254_);
        crate::leanh::lean_dec_ref(v_snap_4252_);
        v___x_4270_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0;
        v___x_4271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4271_, 0, v_log_4253_);
        crate::leanh::lean_ctor_set(v___x_4271_, 1, v___x_4270_);
        v___x_4272_ = lean_task_pure(v___x_4271_);
        return v___x_4272_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(
    mut v_requestedRange_4273_: *mut crate::leanh::LeanObject,
    mut v_snap_4274_: *mut crate::leanh::LeanObject,
    mut v_log_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(
        v_requestedRange_4273_,
        v_snap_4274_,
        v_log_4275_,
    );
    crate::leanh::lean_dec_ref(v_requestedRange_4273_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_collectMessagesInRange(
    mut v_tree_4277_: *mut crate::leanh::LeanObject,
    mut v_requestedRange_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4279_ = crate::leanh::lean_alloc_closure(
        l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4279_, 0, v_requestedRange_4278_);
    v___x_4280_ = l_Lean_MessageLog_empty;
    v___x_4281_ =
        l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_4277_, v___x_4280_, v___f_4279_);
    return v___x_4281_;
}
pub unsafe fn l_Lean_Server_RequestError_methodNotFound(
    mut v_method_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4296_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ = 2;
    v___x_4297_ = l_Lean_Server_RequestError_methodNotFound___closed__0;
    v___x_4298_ = lean_string_append(v___x_4297_, v_method_4295_);
    v___x_4299_ = l_Lean_Server_RequestError_methodNotFound___closed__1;
    v___x_4300_ = lean_string_append(v___x_4298_, v___x_4299_);
    v___x_4301_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4301_, 0, v___x_4300_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4301_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4296_,
    );
    return v___x_4301_;
}
pub unsafe fn l_Lean_Server_RequestError_methodNotFound___boxed(
    mut v_method_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4303_ = l_Lean_Server_RequestError_methodNotFound(v_method_4302_);
    crate::leanh::lean_dec_ref(v_method_4302_);
    return v_res_4303_;
}
pub unsafe fn l_Lean_Server_RequestError_invalidParams(
    mut v_message_4304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = 3;
    v___x_4306_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4306_, 0, v_message_4304_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4306_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4305_,
    );
    return v___x_4306_;
}
pub unsafe fn l_Lean_Server_RequestError_internalError(
    mut v_message_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = 4;
    v___x_4309_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4309_, 0, v_message_4307_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4309_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4308_,
    );
    return v___x_4309_;
}
pub unsafe fn l_Lean_Server_RequestError_ofException(
    mut v_e_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ = l_Lean_Exception_toMessageData(v_e_4319_);
    v___x_4322_ = l_Lean_MessageData_toString(v___x_4321_);
    v___x_4323_ = l_Lean_Server_RequestError_internalError(v___x_4322_);
    v___x_4324_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4323_);
    return v___x_4324_;
}
pub unsafe fn l_Lean_Server_RequestError_ofException___boxed(
    mut v_e_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_Server_RequestError_ofException(v_e_4325_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_Server_RequestError_ofIoError(
    mut v_e_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4329_ = lean_io_error_to_string(v_e_4328_);
    v___x_4330_ = l_Lean_Server_RequestError_internalError(v___x_4329_);
    return v___x_4330_;
}
pub unsafe fn l_Lean_Server_RequestError_toLspResponseError(
    mut v_id_4331_: *mut crate::leanh::LeanObject,
    mut v_e_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_4333_: u8 = 0;
    let mut v_message_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_code_4333_ = crate::leanh::lean_ctor_get_uint8(
        v_e_4332_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_message_4334_ = crate::leanh::lean_ctor_get(v_e_4332_, 0);
    v___x_4335_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_message_4334_);
    v___x_4336_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4336_, 0, v_id_4331_);
    crate::leanh::lean_ctor_set(v___x_4336_, 1, v_message_4334_);
    crate::leanh::lean_ctor_set(v___x_4336_, 2, v___x_4335_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4336_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_code_4333_,
    );
    return v___x_4336_;
}
pub unsafe fn l_Lean_Server_RequestError_toLspResponseError___boxed(
    mut v_id_4337_: *mut crate::leanh::LeanObject,
    mut v_e_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_Server_RequestError_toLspResponseError(v_id_4337_, v_e_4338_);
    crate::leanh::lean_dec_ref(v_e_4338_);
    return v_res_4339_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___redArg(
    mut v_inst_4342_: *mut crate::leanh::LeanObject,
    mut v_params_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: u8 = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4360_: u8 = 0;
    let mut v_a_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4364_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_params_4343_);
                v___x_4344_ = crate::leanh::lean_apply_1(v_inst_4342_, v_params_4343_);
                if crate::leanh::lean_obj_tag(v___x_4344_) == 0 {
                    v_a_4345_ = crate::leanh::lean_ctor_get(v___x_4344_, 0);
                    v_isSharedCheck_4360_ = (!crate::leanh::lean_is_exclusive(v___x_4344_)) as u8;
                    if v_isSharedCheck_4360_ == 0 {
                        v___x_4347_ = v___x_4344_;
                        v_isShared_4348_ = v_isSharedCheck_4360_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4345_);
                        crate::leanh::lean_dec(v___x_4344_);
                        v___x_4347_ = crate::leanh::lean_box(0);
                        v_isShared_4348_ = v_isSharedCheck_4360_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_params_4343_);
                    v_a_4361_ = crate::leanh::lean_ctor_get(v___x_4344_, 0);
                    v_isSharedCheck_4368_ = (!crate::leanh::lean_is_exclusive(v___x_4344_)) as u8;
                    if v_isSharedCheck_4368_ == 0 {
                        v___x_4363_ = v___x_4344_;
                        v_isShared_4364_ = v_isSharedCheck_4368_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4361_);
                        crate::leanh::lean_dec(v___x_4344_);
                        v___x_4363_ = crate::leanh::lean_box(0);
                        v_isShared_4364_ = v_isSharedCheck_4368_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4349_ = 3;
                v___x_4350_ = l_Lean_Server_parseRequestParams___redArg___closed__0;
                v___x_4351_ = l_Lean_Json_compress(v_params_4343_);
                v___x_4352_ = lean_string_append(v___x_4350_, v___x_4351_);
                crate::leanh::lean_dec_ref(v___x_4351_);
                v___x_4353_ = l_Lean_Server_parseRequestParams___redArg___closed__1;
                v___x_4354_ = lean_string_append(v___x_4352_, v___x_4353_);
                v___x_4355_ = lean_string_append(v___x_4354_, v_a_4345_);
                crate::leanh::lean_dec(v_a_4345_);
                v___x_4356_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4356_, 0, v___x_4355_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4356_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4349_,
                );
                if v_isShared_4348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4347_, 0, v___x_4356_);
                    v___x_4358_ = v___x_4347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
                    v___x_4358_ = v_reuseFailAlloc_4359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4358_;
            }
            3 => {
                if v_isShared_4364_ == 0 {
                    v___x_4366_ = v___x_4363_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
                    v___x_4366_ = v_reuseFailAlloc_4367_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_parseRequestParams(
    mut v_paramType_4369_: *mut crate::leanh::LeanObject,
    mut v_inst_4370_: *mut crate::leanh::LeanObject,
    mut v_params_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4372_ = l_Lean_Server_parseRequestParams___redArg(v_inst_4370_, v_params_4371_);
    return v___x_4372_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(
    mut v_x_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4373_) == 0 {
        let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4374_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4374_;
    } else {
        let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4375_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4375_;
    }
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(
    mut v_x_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4377_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_4376_);
    crate::leanh::lean_dec_ref(v_x_4376_);
    return v_res_4377_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorIdx(
    mut v_00_u03b1_4378_: *mut crate::leanh::LeanObject,
    mut v_x_4379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_4379_);
    return v___x_4380_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(
    mut v_00_u03b1_4381_: *mut crate::leanh::LeanObject,
    mut v_x_4382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4383_ = l_Lean_Server_ServerRequestResponse_ctorIdx(v_00_u03b1_4381_, v_x_4382_);
    crate::leanh::lean_dec_ref(v_x_4382_);
    return v_res_4383_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorElim___redArg(
    mut v_t_4384_: *mut crate::leanh::LeanObject,
    mut v_k_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4384_) == 0 {
        let mut v_response_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_response_4386_ = crate::leanh::lean_ctor_get(v_t_4384_, 0);
        crate::leanh::lean_inc(v_response_4386_);
        crate::leanh::lean_dec_ref_known(v_t_4384_, 1);
        v___x_4387_ = crate::leanh::lean_apply_1(v_k_4385_, v_response_4386_);
        return v___x_4387_;
    } else {
        let mut v_code_4388_: u8 = 0;
        let mut v_message_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_code_4388_ = crate::leanh::lean_ctor_get_uint8(
            v_t_4384_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        v_message_4389_ = crate::leanh::lean_ctor_get(v_t_4384_, 0);
        crate::leanh::lean_inc_ref(v_message_4389_);
        crate::leanh::lean_dec_ref_known(v_t_4384_, 1);
        v___x_4390_ = crate::leanh::lean_box((v_code_4388_) as usize);
        v___x_4391_ = crate::leanh::lean_apply_2(v_k_4385_, v___x_4390_, v_message_4389_);
        return v___x_4391_;
    }
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorElim(
    mut v_00_u03b1_4392_: *mut crate::leanh::LeanObject,
    mut v_motive_4393_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4394_: *mut crate::leanh::LeanObject,
    mut v_t_4395_: *mut crate::leanh::LeanObject,
    mut v_h_4396_: *mut crate::leanh::LeanObject,
    mut v_k_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_4395_, v_k_4397_);
    return v___x_4398_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_ctorElim___boxed(
    mut v_00_u03b1_4399_: *mut crate::leanh::LeanObject,
    mut v_motive_4400_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4401_: *mut crate::leanh::LeanObject,
    mut v_t_4402_: *mut crate::leanh::LeanObject,
    mut v_h_4403_: *mut crate::leanh::LeanObject,
    mut v_k_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_Server_ServerRequestResponse_ctorElim(
        v_00_u03b1_4399_,
        v_motive_4400_,
        v_ctorIdx_4401_,
        v_t_4402_,
        v_h_4403_,
        v_k_4404_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4401_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_success_elim___redArg(
    mut v_t_4406_: *mut crate::leanh::LeanObject,
    mut v_success_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4408_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_4406_, v_success_4407_);
    return v___x_4408_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_success_elim(
    mut v_00_u03b1_4409_: *mut crate::leanh::LeanObject,
    mut v_motive_4410_: *mut crate::leanh::LeanObject,
    mut v_t_4411_: *mut crate::leanh::LeanObject,
    mut v_h_4412_: *mut crate::leanh::LeanObject,
    mut v_success_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_4411_, v_success_4413_);
    return v___x_4414_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_failure_elim___redArg(
    mut v_t_4415_: *mut crate::leanh::LeanObject,
    mut v_failure_4416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4417_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_4415_, v_failure_4416_);
    return v___x_4417_;
}
pub unsafe fn l_Lean_Server_ServerRequestResponse_failure_elim(
    mut v_00_u03b1_4418_: *mut crate::leanh::LeanObject,
    mut v_motive_4419_: *mut crate::leanh::LeanObject,
    mut v_t_4420_: *mut crate::leanh::LeanObject,
    mut v_h_4421_: *mut crate::leanh::LeanObject,
    mut v_failure_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_4420_, v_failure_4422_);
    return v___x_4423_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerRequestResponse_default(
    mut v_00_u03b1_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4428_ = l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0;
    return v___x_4428_;
}
pub unsafe fn _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ =
        l_Lean_Server_instInhabitedServerRequestResponse_default(crate::leanh::lean_box(0));
    return v___x_4429_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerRequestResponse(
    mut v_a_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedServerRequestResponse___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once),
        _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0,
    );
    return v___x_4431_;
}
pub unsafe fn l_Lean_Server_RequestM_run___redArg(
    mut v_act_4432_: *mut crate::leanh::LeanObject,
    mut v_rc_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = crate::leanh::lean_apply_2(v_act_4432_, v_rc_4433_, crate::leanh::lean_box(0));
    return v___x_4435_;
}
pub unsafe fn l_Lean_Server_RequestM_run___redArg___boxed(
    mut v_act_4436_: *mut crate::leanh::LeanObject,
    mut v_rc_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_Lean_Server_RequestM_run___redArg(v_act_4436_, v_rc_4437_);
    return v_res_4439_;
}
pub unsafe fn l_Lean_Server_RequestM_run(
    mut v_00_u03b1_4440_: *mut crate::leanh::LeanObject,
    mut v_act_4441_: *mut crate::leanh::LeanObject,
    mut v_rc_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4444_ = crate::leanh::lean_apply_2(v_act_4441_, v_rc_4442_, crate::leanh::lean_box(0));
    return v___x_4444_;
}
pub unsafe fn l_Lean_Server_RequestM_run___boxed(
    mut v_00_u03b1_4445_: *mut crate::leanh::LeanObject,
    mut v_act_4446_: *mut crate::leanh::LeanObject,
    mut v_rc_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lean_Server_RequestM_run(v_00_u03b1_4445_, v_act_4446_, v_rc_4447_);
    return v_res_4449_;
}
pub unsafe fn l_Lean_Server_RequestTask_pure___redArg(
    mut v_a_4450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4451_, 0, v_a_4450_);
    v___x_4452_ = lean_task_pure(v___x_4451_);
    return v___x_4452_;
}
pub unsafe fn l_Lean_Server_RequestTask_pure(
    mut v_00_u03b1_4453_: *mut crate::leanh::LeanObject,
    mut v_a_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4455_, 0, v_a_4454_);
    v___x_4456_ = lean_task_pure(v___x_4455_);
    return v___x_4456_;
}
pub unsafe fn l_Lean_Server_instMonadLiftIORequestM___lam__0(
    mut v_00_u03b1_4457_: *mut crate::leanh::LeanObject,
    mut v_x_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut v_a_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4461_ = crate::leanh::lean_apply_1(v_x_4458_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4461_) == 0 {
                    v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                    v_isSharedCheck_4469_ = (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                    if v_isSharedCheck_4469_ == 0 {
                        v___x_4464_ = v___x_4461_;
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4462_);
                        crate::leanh::lean_dec(v___x_4461_);
                        v___x_4464_ = crate::leanh::lean_box(0);
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4470_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                    v_isSharedCheck_4478_ = (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4472_ = v___x_4461_;
                        v_isShared_4473_ = v_isSharedCheck_4478_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4470_);
                        crate::leanh::lean_dec(v___x_4461_);
                        v___x_4472_ = crate::leanh::lean_box(0);
                        v_isShared_4473_ = v_isSharedCheck_4478_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4465_ == 0 {
                    v___x_4467_ = v___x_4464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
                    v___x_4467_ = v_reuseFailAlloc_4468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4467_;
            }
            3 => {
                v___x_4474_ = l_Lean_Server_RequestError_ofIoError(v_a_4470_);
                if v_isShared_4473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4472_, 0, v___x_4474_);
                    v___x_4476_ = v___x_4472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(
    mut v_00_u03b1_4479_: *mut crate::leanh::LeanObject,
    mut v_x_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4483_ =
        l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_4479_, v_x_4480_, v___y_4481_);
    crate::leanh::lean_dec_ref(v___y_4481_);
    return v_res_4483_;
}
pub unsafe fn l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(
    mut v_00_u03b1_4486_: *mut crate::leanh::LeanObject,
    mut v_x_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut v_a_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4504_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4490_ = crate::leanh::lean_apply_1(v_x_4487_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_a_4491_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4498_ = (!crate::leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4498_ == 0 {
                        v___x_4493_ = v___x_4490_;
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4491_);
                        crate::leanh::lean_dec(v___x_4490_);
                        v___x_4493_ = crate::leanh::lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4499_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    crate::leanh::lean_inc(v_a_4499_);
                    crate::leanh::lean_dec_ref_known(v___x_4490_, 1);
                    v___x_4500_ = l_Lean_Server_RequestError_ofException(v_a_4499_);
                    v_a_4501_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                    v_isSharedCheck_4508_ = (!crate::leanh::lean_is_exclusive(v___x_4500_)) as u8;
                    if v_isSharedCheck_4508_ == 0 {
                        v___x_4503_ = v___x_4500_;
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4501_);
                        crate::leanh::lean_dec(v___x_4500_);
                        v___x_4503_ = crate::leanh::lean_box(0);
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4494_ == 0 {
                    v___x_4496_ = v___x_4493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
                    v___x_4496_ = v_reuseFailAlloc_4497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4496_;
            }
            3 => {
                if v_isShared_4504_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4503_, 1);
                    v___x_4506_ = v___x_4503_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
                    v___x_4506_ = v_reuseFailAlloc_4507_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(
    mut v_00_u03b1_4509_: *mut crate::leanh::LeanObject,
    mut v_x_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4513_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(
        v_00_u03b1_4509_,
        v_x_4510_,
        v___y_4511_,
    );
    crate::leanh::lean_dec_ref(v___y_4511_);
    return v_res_4513_;
}
pub unsafe fn l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(
    mut v_00_u03b1_4516_: *mut crate::leanh::LeanObject,
    mut v_x_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancelTk_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_4520_ = crate::leanh::lean_ctor_get(v___y_4518_, 4);
                crate::leanh::lean_inc_ref(v_cancelTk_4520_);
                v___x_4521_ = crate::leanh::lean_apply_2(
                    v_x_4517_,
                    v_cancelTk_4520_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4521_) == 0 {
                    v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                    v_isSharedCheck_4534_ = (!crate::leanh::lean_is_exclusive(v___x_4521_)) as u8;
                    if v_isSharedCheck_4534_ == 0 {
                        v___x_4524_ = v___x_4521_;
                        v_isShared_4525_ = v_isSharedCheck_4534_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4522_);
                        crate::leanh::lean_dec(v___x_4521_);
                        v___x_4524_ = crate::leanh::lean_box(0);
                        v_isShared_4525_ = v_isSharedCheck_4534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                    v_isSharedCheck_4543_ = (!crate::leanh::lean_is_exclusive(v___x_4521_)) as u8;
                    if v_isSharedCheck_4543_ == 0 {
                        v___x_4537_ = v___x_4521_;
                        v_isShared_4538_ = v_isSharedCheck_4543_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4535_);
                        crate::leanh::lean_dec(v___x_4521_);
                        v___x_4537_ = crate::leanh::lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4543_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4522_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_4522_, 1);
                    v___x_4526_ = l_Lean_Server_RequestError_requestCancelled;
                    if v_isShared_4525_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4524_, 1);
                        crate::leanh::lean_ctor_set(v___x_4524_, 0, v___x_4526_);
                        v___x_4528_ = v___x_4524_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4526_);
                        v___x_4528_ = v_reuseFailAlloc_4529_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4530_ = crate::leanh::lean_ctor_get(v_a_4522_, 0);
                    crate::leanh::lean_inc(v_a_4530_);
                    crate::leanh::lean_dec_ref_known(v_a_4522_, 1);
                    if v_isShared_4525_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4524_, 0, v_a_4530_);
                        v___x_4532_ = v___x_4524_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4530_);
                        v___x_4532_ = v_reuseFailAlloc_4533_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4528_;
            }
            3 => {
                return v___x_4532_;
            }
            4 => {
                v___x_4539_ = l_Lean_Server_RequestError_ofIoError(v_a_4535_);
                if v_isShared_4538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4537_, 0, v___x_4539_);
                    v___x_4541_ = v___x_4537_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
                    v___x_4541_ = v_reuseFailAlloc_4542_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(
    mut v_00_u03b1_4544_: *mut crate::leanh::LeanObject,
    mut v_x_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(
        v_00_u03b1_4544_,
        v_x_4545_,
        v___y_4546_,
    );
    crate::leanh::lean_dec_ref(v___y_4546_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_Server_RequestM_runInIO___redArg(
    mut v_x_4551_: *mut crate::leanh::LeanObject,
    mut v_ctx_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4558_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut v_a_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v_message_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4554_ =
                    crate::leanh::lean_apply_2(v_x_4551_, v_ctx_4552_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4554_) == 0 {
                    v_a_4555_ = crate::leanh::lean_ctor_get(v___x_4554_, 0);
                    v_isSharedCheck_4562_ = (!crate::leanh::lean_is_exclusive(v___x_4554_)) as u8;
                    if v_isSharedCheck_4562_ == 0 {
                        v___x_4557_ = v___x_4554_;
                        v_isShared_4558_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4555_);
                        crate::leanh::lean_dec(v___x_4554_);
                        v___x_4557_ = crate::leanh::lean_box(0);
                        v_isShared_4558_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4563_ = crate::leanh::lean_ctor_get(v___x_4554_, 0);
                    v_isSharedCheck_4572_ = (!crate::leanh::lean_is_exclusive(v___x_4554_)) as u8;
                    if v_isSharedCheck_4572_ == 0 {
                        v___x_4565_ = v___x_4554_;
                        v_isShared_4566_ = v_isSharedCheck_4572_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4563_);
                        crate::leanh::lean_dec(v___x_4554_);
                        v___x_4565_ = crate::leanh::lean_box(0);
                        v_isShared_4566_ = v_isSharedCheck_4572_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4558_ == 0 {
                    v___x_4560_ = v___x_4557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
                    v___x_4560_ = v_reuseFailAlloc_4561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4560_;
            }
            3 => {
                v_message_4567_ = crate::leanh::lean_ctor_get(v_a_4563_, 0);
                crate::leanh::lean_inc_ref(v_message_4567_);
                crate::leanh::lean_dec(v_a_4563_);
                v___x_4568_ = lean_mk_io_user_error(v_message_4567_);
                if v_isShared_4566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4565_, 0, v___x_4568_);
                    v___x_4570_ = v___x_4565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_runInIO___redArg___boxed(
    mut v_x_4573_: *mut crate::leanh::LeanObject,
    mut v_ctx_4574_: *mut crate::leanh::LeanObject,
    mut v_a_4575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4576_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_4573_, v_ctx_4574_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_Server_RequestM_runInIO(
    mut v_00_u03b1_4577_: *mut crate::leanh::LeanObject,
    mut v_x_4578_: *mut crate::leanh::LeanObject,
    mut v_ctx_4579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4581_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_4578_, v_ctx_4579_);
    return v___x_4581_;
}
pub unsafe fn l_Lean_Server_RequestM_runInIO___boxed(
    mut v_00_u03b1_4582_: *mut crate::leanh::LeanObject,
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_ctx_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4586_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_4582_, v_x_4583_, v_ctx_4584_);
    return v_res_4586_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___redArg___lam__0(
    mut v_toPure_4587_: *mut crate::leanh::LeanObject,
    mut v_rc_4588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_doc_4589_ = crate::leanh::lean_ctor_get(v_rc_4588_, 1);
    crate::leanh::lean_inc_ref(v_doc_4589_);
    crate::leanh::lean_dec_ref(v_rc_4588_);
    v___x_4590_ =
        crate::leanh::lean_apply_2(v_toPure_4587_, crate::leanh::lean_box(0), v_doc_4589_);
    return v___x_4590_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___redArg(
    mut v_inst_4591_: *mut crate::leanh::LeanObject,
    mut v_inst_4592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4593_ = crate::leanh::lean_ctor_get(v_inst_4591_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4593_);
    v_toBind_4594_ = crate::leanh::lean_ctor_get(v_inst_4591_, 1);
    crate::leanh::lean_inc(v_toBind_4594_);
    crate::leanh::lean_dec_ref(v_inst_4591_);
    v_toPure_4595_ = crate::leanh::lean_ctor_get(v_toApplicative_4593_, 1);
    crate::leanh::lean_inc(v_toPure_4595_);
    crate::leanh::lean_dec_ref(v_toApplicative_4593_);
    v___f_4596_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_readDoc___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4596_, 0, v_toPure_4595_);
    v___x_4597_ = crate::leanh::lean_apply_4(
        v_toBind_4594_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4592_,
        v___f_4596_,
    );
    return v___x_4597_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc(
    mut v_m_4598_: *mut crate::leanh::LeanObject,
    mut v_inst_4599_: *mut crate::leanh::LeanObject,
    mut v_inst_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_4599_, v_inst_4600_);
    return v___x_4601_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask___redArg___lam__0(
    mut v_t_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4603_);
    v___x_4605_ = crate::leanh::lean_apply_2(v_t_4602_, v_a_4603_, crate::leanh::lean_box(0));
    return v___x_4605_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(
    mut v_t_4606_: *mut crate::leanh::LeanObject,
    mut v_a_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_4606_, v_a_4607_);
    crate::leanh::lean_dec_ref(v_a_4607_);
    return v_res_4609_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask___redArg(
    mut v_t_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4611_);
    v___f_4613_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4613_, 0, v_t_4610_);
    crate::leanh::lean_closure_set(v___f_4613_, 1, v_a_4611_);
    v___x_4614_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_4613_);
    v___x_4615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4615_, 0, v___x_4614_);
    return v___x_4615_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask___redArg___boxed(
    mut v_t_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_Server_RequestM_asTask___redArg(v_t_4616_, v_a_4617_);
    crate::leanh::lean_dec_ref(v_a_4617_);
    return v_res_4619_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask(
    mut v_00_u03b1_4620_: *mut crate::leanh::LeanObject,
    mut v_t_4621_: *mut crate::leanh::LeanObject,
    mut v_a_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = l_Lean_Server_RequestM_asTask___redArg(v_t_4621_, v_a_4622_);
    return v___x_4624_;
}
pub unsafe fn l_Lean_Server_RequestM_asTask___boxed(
    mut v_00_u03b1_4625_: *mut crate::leanh::LeanObject,
    mut v_t_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4629_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_4625_, v_t_4626_, v_a_4627_);
    crate::leanh::lean_dec_ref(v_a_4627_);
    return v_res_4629_;
}
pub unsafe fn l_Lean_Server_RequestM_pureTask___redArg(
    mut v_t_4630_: *mut crate::leanh::LeanObject,
    mut v_a_4631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut v_a_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_4631_);
                v___x_4633_ =
                    crate::leanh::lean_apply_2(v_t_4630_, v_a_4631_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4633_) == 0 {
                    v_a_4634_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                    v_isSharedCheck_4643_ = (!crate::leanh::lean_is_exclusive(v___x_4633_)) as u8;
                    if v_isSharedCheck_4643_ == 0 {
                        v___x_4636_ = v___x_4633_;
                        v_isShared_4637_ = v_isSharedCheck_4643_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4634_);
                        crate::leanh::lean_dec(v___x_4633_);
                        v___x_4636_ = crate::leanh::lean_box(0);
                        v_isShared_4637_ = v_isSharedCheck_4643_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4644_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                    v_isSharedCheck_4651_ = (!crate::leanh::lean_is_exclusive(v___x_4633_)) as u8;
                    if v_isSharedCheck_4651_ == 0 {
                        v___x_4646_ = v___x_4633_;
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4644_);
                        crate::leanh::lean_dec(v___x_4633_);
                        v___x_4646_ = crate::leanh::lean_box(0);
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4638_, 0, v_a_4634_);
                v___x_4639_ = lean_task_pure(v___x_4638_);
                if v_isShared_4637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4636_, 0, v___x_4639_);
                    v___x_4641_ = v___x_4636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
                    v___x_4641_ = v_reuseFailAlloc_4642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4641_;
            }
            3 => {
                if v_isShared_4647_ == 0 {
                    v___x_4649_ = v___x_4646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_pureTask___redArg___boxed(
    mut v_t_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_4652_, v_a_4653_);
    crate::leanh::lean_dec_ref(v_a_4653_);
    return v_res_4655_;
}
pub unsafe fn l_Lean_Server_RequestM_pureTask(
    mut v_00_u03b1_4656_: *mut crate::leanh::LeanObject,
    mut v_t_4657_: *mut crate::leanh::LeanObject,
    mut v_a_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4660_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_4657_, v_a_4658_);
    return v___x_4660_;
}
pub unsafe fn l_Lean_Server_RequestM_pureTask___boxed(
    mut v_00_u03b1_4661_: *mut crate::leanh::LeanObject,
    mut v_t_4662_: *mut crate::leanh::LeanObject,
    mut v_a_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4665_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_4661_, v_t_4662_, v_a_4663_);
    crate::leanh::lean_dec_ref(v_a_4663_);
    return v_res_4665_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(
    mut v_f_4666_: *mut crate::leanh::LeanObject,
    mut v_a_4667_: *mut crate::leanh::LeanObject,
    mut v_x_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4667_);
    v___x_4670_ =
        crate::leanh::lean_apply_3(v_f_4666_, v_x_4668_, v_a_4667_, crate::leanh::lean_box(0));
    return v___x_4670_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(
    mut v_f_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_x_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ =
        l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_4671_, v_a_4672_, v_x_4673_);
    crate::leanh::lean_dec_ref(v_a_4672_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap___redArg(
    mut v_t_4676_: *mut crate::leanh::LeanObject,
    mut v_f_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4678_);
    v___f_4680_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4680_, 0, v_f_4677_);
    crate::leanh::lean_closure_set(v___f_4680_, 1, v_a_4678_);
    v___x_4681_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_4680_, v_t_4676_);
    v___x_4682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4682_, 0, v___x_4681_);
    return v___x_4682_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(
    mut v_t_4683_: *mut crate::leanh::LeanObject,
    mut v_f_4684_: *mut crate::leanh::LeanObject,
    mut v_a_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_4683_, v_f_4684_, v_a_4685_);
    crate::leanh::lean_dec_ref(v_a_4685_);
    return v_res_4687_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap(
    mut v_00_u03b1_4688_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4689_: *mut crate::leanh::LeanObject,
    mut v_t_4690_: *mut crate::leanh::LeanObject,
    mut v_f_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4694_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_4690_, v_f_4691_, v_a_4692_);
    return v___x_4694_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCheap___boxed(
    mut v_00_u03b1_4695_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4696_: *mut crate::leanh::LeanObject,
    mut v_t_4697_: *mut crate::leanh::LeanObject,
    mut v_f_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4701_ = l_Lean_Server_RequestM_mapTaskCheap(
        v_00_u03b1_4695_,
        v_00_u03b2_4696_,
        v_t_4697_,
        v_f_4698_,
        v_a_4699_,
    );
    crate::leanh::lean_dec_ref(v_a_4699_);
    return v_res_4701_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCostly___redArg(
    mut v_t_4702_: *mut crate::leanh::LeanObject,
    mut v_f_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4704_);
    v___f_4706_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4706_, 0, v_f_4703_);
    crate::leanh::lean_closure_set(v___f_4706_, 1, v_a_4704_);
    v___x_4707_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_4706_, v_t_4702_);
    v___x_4708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4708_, 0, v___x_4707_);
    return v___x_4708_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(
    mut v_t_4709_: *mut crate::leanh::LeanObject,
    mut v_f_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4713_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_4709_, v_f_4710_, v_a_4711_);
    crate::leanh::lean_dec_ref(v_a_4711_);
    return v_res_4713_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCostly(
    mut v_00_u03b1_4714_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4715_: *mut crate::leanh::LeanObject,
    mut v_t_4716_: *mut crate::leanh::LeanObject,
    mut v_f_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4720_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_4716_, v_f_4717_, v_a_4718_);
    return v___x_4720_;
}
pub unsafe fn l_Lean_Server_RequestM_mapTaskCostly___boxed(
    mut v_00_u03b1_4721_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4722_: *mut crate::leanh::LeanObject,
    mut v_t_4723_: *mut crate::leanh::LeanObject,
    mut v_f_4724_: *mut crate::leanh::LeanObject,
    mut v_a_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4727_ = l_Lean_Server_RequestM_mapTaskCostly(
        v_00_u03b1_4721_,
        v_00_u03b2_4722_,
        v_t_4723_,
        v_f_4724_,
        v_a_4725_,
    );
    crate::leanh::lean_dec_ref(v_a_4725_);
    return v_res_4727_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(
    mut v_f_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
    mut v_x_4730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4729_);
    v___x_4732_ =
        crate::leanh::lean_apply_3(v_f_4728_, v_x_4730_, v_a_4729_, crate::leanh::lean_box(0));
    return v___x_4732_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(
    mut v_f_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_x_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4737_ =
        l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_4733_, v_a_4734_, v_x_4735_);
    crate::leanh::lean_dec_ref(v_a_4734_);
    return v_res_4737_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap___redArg(
    mut v_t_4738_: *mut crate::leanh::LeanObject,
    mut v_f_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4740_);
    v___f_4742_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4742_, 0, v_f_4739_);
    crate::leanh::lean_closure_set(v___f_4742_, 1, v_a_4740_);
    v___x_4743_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_4738_, v___f_4742_);
    v___x_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4744_, 0, v___x_4743_);
    return v___x_4744_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(
    mut v_t_4745_: *mut crate::leanh::LeanObject,
    mut v_f_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4749_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_4745_, v_f_4746_, v_a_4747_);
    crate::leanh::lean_dec_ref(v_a_4747_);
    return v_res_4749_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap(
    mut v_00_u03b1_4750_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4751_: *mut crate::leanh::LeanObject,
    mut v_t_4752_: *mut crate::leanh::LeanObject,
    mut v_f_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4756_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_4752_, v_f_4753_, v_a_4754_);
    return v___x_4756_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCheap___boxed(
    mut v_00_u03b1_4757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4758_: *mut crate::leanh::LeanObject,
    mut v_t_4759_: *mut crate::leanh::LeanObject,
    mut v_f_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_Server_RequestM_bindTaskCheap(
        v_00_u03b1_4757_,
        v_00_u03b2_4758_,
        v_t_4759_,
        v_f_4760_,
        v_a_4761_,
    );
    crate::leanh::lean_dec_ref(v_a_4761_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCostly___redArg(
    mut v_t_4764_: *mut crate::leanh::LeanObject,
    mut v_f_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4766_);
    v___f_4768_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4768_, 0, v_f_4765_);
    crate::leanh::lean_closure_set(v___f_4768_, 1, v_a_4766_);
    v___x_4769_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_4764_, v___f_4768_);
    v___x_4770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4770_, 0, v___x_4769_);
    return v___x_4770_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(
    mut v_t_4771_: *mut crate::leanh::LeanObject,
    mut v_f_4772_: *mut crate::leanh::LeanObject,
    mut v_a_4773_: *mut crate::leanh::LeanObject,
    mut v_a_4774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4775_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_4771_, v_f_4772_, v_a_4773_);
    crate::leanh::lean_dec_ref(v_a_4773_);
    return v_res_4775_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCostly(
    mut v_00_u03b1_4776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4777_: *mut crate::leanh::LeanObject,
    mut v_t_4778_: *mut crate::leanh::LeanObject,
    mut v_f_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4782_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_4778_, v_f_4779_, v_a_4780_);
    return v___x_4782_;
}
pub unsafe fn l_Lean_Server_RequestM_bindTaskCostly___boxed(
    mut v_00_u03b1_4783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4784_: *mut crate::leanh::LeanObject,
    mut v_t_4785_: *mut crate::leanh::LeanObject,
    mut v_f_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Lean_Server_RequestM_bindTaskCostly(
        v_00_u03b1_4783_,
        v_00_u03b2_4784_,
        v_t_4785_,
        v_f_4786_,
        v_a_4787_,
    );
    crate::leanh::lean_dec_ref(v_a_4787_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(
    mut v_f_4790_: *mut crate::leanh::LeanObject,
    mut v_x_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4797_: u8 = 0;
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut v_a_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4791_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_4790_);
                    v_a_4794_ = crate::leanh::lean_ctor_get(v_x_4791_, 0);
                    v_isSharedCheck_4801_ = (!crate::leanh::lean_is_exclusive(v_x_4791_)) as u8;
                    if v_isSharedCheck_4801_ == 0 {
                        v___x_4796_ = v_x_4791_;
                        v_isShared_4797_ = v_isSharedCheck_4801_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4794_);
                        crate::leanh::lean_dec(v_x_4791_);
                        v___x_4796_ = crate::leanh::lean_box(0);
                        v_isShared_4797_ = v_isSharedCheck_4801_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4802_ = crate::leanh::lean_ctor_get(v_x_4791_, 0);
                    crate::leanh::lean_inc(v_a_4802_);
                    crate::leanh::lean_dec_ref_known(v_x_4791_, 1);
                    crate::leanh::lean_inc_ref(v___y_4792_);
                    v___x_4803_ = crate::leanh::lean_apply_3(
                        v_f_4790_,
                        v_a_4802_,
                        v___y_4792_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4803_;
                }
            }
            1 => {
                if v_isShared_4797_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4796_, 1);
                    v___x_4799_ = v___x_4796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
                    v___x_4799_ = v_reuseFailAlloc_4800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(
    mut v_f_4804_: *mut crate::leanh::LeanObject,
    mut v_x_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(
        v_f_4804_,
        v_x_4805_,
        v___y_4806_,
    );
    crate::leanh::lean_dec_ref(v___y_4806_);
    return v_res_4808_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(
    mut v_t_4809_: *mut crate::leanh::LeanObject,
    mut v_f_4810_: *mut crate::leanh::LeanObject,
    mut v_a_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4813_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4813_, 0, v_f_4810_);
    v___x_4814_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_4809_, v___f_4813_, v_a_4811_);
    return v___x_4814_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(
    mut v_t_4815_: *mut crate::leanh::LeanObject,
    mut v_f_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4819_ =
        l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_4815_, v_f_4816_, v_a_4817_);
    crate::leanh::lean_dec_ref(v_a_4817_);
    return v_res_4819_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap(
    mut v_00_u03b1_4820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4821_: *mut crate::leanh::LeanObject,
    mut v_t_4822_: *mut crate::leanh::LeanObject,
    mut v_f_4823_: *mut crate::leanh::LeanObject,
    mut v_a_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4826_ =
        l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_4822_, v_f_4823_, v_a_4824_);
    return v___x_4826_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(
    mut v_00_u03b1_4827_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4828_: *mut crate::leanh::LeanObject,
    mut v_t_4829_: *mut crate::leanh::LeanObject,
    mut v_f_4830_: *mut crate::leanh::LeanObject,
    mut v_a_4831_: *mut crate::leanh::LeanObject,
    mut v_a_4832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4833_ = l_Lean_Server_RequestM_mapRequestTaskCheap(
        v_00_u03b1_4827_,
        v_00_u03b2_4828_,
        v_t_4829_,
        v_f_4830_,
        v_a_4831_,
    );
    crate::leanh::lean_dec_ref(v_a_4831_);
    return v_res_4833_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(
    mut v_t_4834_: *mut crate::leanh::LeanObject,
    mut v_f_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4838_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4838_, 0, v_f_4835_);
    v___x_4839_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_4834_, v___f_4838_, v_a_4836_);
    return v___x_4839_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(
    mut v_t_4840_: *mut crate::leanh::LeanObject,
    mut v_f_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4844_ =
        l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_4840_, v_f_4841_, v_a_4842_);
    crate::leanh::lean_dec_ref(v_a_4842_);
    return v_res_4844_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCostly(
    mut v_00_u03b1_4845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4846_: *mut crate::leanh::LeanObject,
    mut v_t_4847_: *mut crate::leanh::LeanObject,
    mut v_f_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ =
        l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_4847_, v_f_4848_, v_a_4849_);
    return v___x_4851_;
}
pub unsafe fn l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(
    mut v_00_u03b1_4852_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4853_: *mut crate::leanh::LeanObject,
    mut v_t_4854_: *mut crate::leanh::LeanObject,
    mut v_f_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4858_ = l_Lean_Server_RequestM_mapRequestTaskCostly(
        v_00_u03b1_4852_,
        v_00_u03b2_4853_,
        v_t_4854_,
        v_f_4855_,
        v_a_4856_,
    );
    crate::leanh::lean_dec_ref(v_a_4856_);
    return v_res_4858_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(
    mut v_f_4859_: *mut crate::leanh::LeanObject,
    mut v_x_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_a_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4860_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_4859_);
                    v_a_4863_ = crate::leanh::lean_ctor_get(v_x_4860_, 0);
                    v_isSharedCheck_4870_ = (!crate::leanh::lean_is_exclusive(v_x_4860_)) as u8;
                    if v_isSharedCheck_4870_ == 0 {
                        v___x_4865_ = v_x_4860_;
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4863_);
                        crate::leanh::lean_dec(v_x_4860_);
                        v___x_4865_ = crate::leanh::lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4871_ = crate::leanh::lean_ctor_get(v_x_4860_, 0);
                    crate::leanh::lean_inc(v_a_4871_);
                    crate::leanh::lean_dec_ref_known(v_x_4860_, 1);
                    crate::leanh::lean_inc_ref(v___y_4861_);
                    v___x_4872_ = crate::leanh::lean_apply_3(
                        v_f_4859_,
                        v_a_4871_,
                        v___y_4861_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4872_;
                }
            }
            1 => {
                if v_isShared_4866_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4865_, 1);
                    v___x_4868_ = v___x_4865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(
    mut v_f_4873_: *mut crate::leanh::LeanObject,
    mut v_x_4874_: *mut crate::leanh::LeanObject,
    mut v___y_4875_: *mut crate::leanh::LeanObject,
    mut v___y_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4877_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(
        v_f_4873_,
        v_x_4874_,
        v___y_4875_,
    );
    crate::leanh::lean_dec_ref(v___y_4875_);
    return v_res_4877_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(
    mut v_t_4878_: *mut crate::leanh::LeanObject,
    mut v_f_4879_: *mut crate::leanh::LeanObject,
    mut v_a_4880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4882_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4882_, 0, v_f_4879_);
    v___x_4883_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_4878_, v___f_4882_, v_a_4880_);
    return v___x_4883_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(
    mut v_t_4884_: *mut crate::leanh::LeanObject,
    mut v_f_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4888_ =
        l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_4884_, v_f_4885_, v_a_4886_);
    crate::leanh::lean_dec_ref(v_a_4886_);
    return v_res_4888_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap(
    mut v_00_u03b1_4889_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4890_: *mut crate::leanh::LeanObject,
    mut v_t_4891_: *mut crate::leanh::LeanObject,
    mut v_f_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4895_ =
        l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_4891_, v_f_4892_, v_a_4893_);
    return v___x_4895_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(
    mut v_00_u03b1_4896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4897_: *mut crate::leanh::LeanObject,
    mut v_t_4898_: *mut crate::leanh::LeanObject,
    mut v_f_4899_: *mut crate::leanh::LeanObject,
    mut v_a_4900_: *mut crate::leanh::LeanObject,
    mut v_a_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4902_ = l_Lean_Server_RequestM_bindRequestTaskCheap(
        v_00_u03b1_4896_,
        v_00_u03b2_4897_,
        v_t_4898_,
        v_f_4899_,
        v_a_4900_,
    );
    crate::leanh::lean_dec_ref(v_a_4900_);
    return v_res_4902_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(
    mut v_t_4903_: *mut crate::leanh::LeanObject,
    mut v_f_4904_: *mut crate::leanh::LeanObject,
    mut v_a_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4907_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4907_, 0, v_f_4904_);
    v___x_4908_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_4903_, v___f_4907_, v_a_4905_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(
    mut v_t_4909_: *mut crate::leanh::LeanObject,
    mut v_f_4910_: *mut crate::leanh::LeanObject,
    mut v_a_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ =
        l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_4909_, v_f_4910_, v_a_4911_);
    crate::leanh::lean_dec_ref(v_a_4911_);
    return v_res_4913_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCostly(
    mut v_00_u03b1_4914_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4915_: *mut crate::leanh::LeanObject,
    mut v_t_4916_: *mut crate::leanh::LeanObject,
    mut v_f_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ =
        l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_4916_, v_f_4917_, v_a_4918_);
    return v___x_4920_;
}
pub unsafe fn l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(
    mut v_00_u03b1_4921_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4922_: *mut crate::leanh::LeanObject,
    mut v_t_4923_: *mut crate::leanh::LeanObject,
    mut v_f_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4927_ = l_Lean_Server_RequestM_bindRequestTaskCostly(
        v_00_u03b1_4921_,
        v_00_u03b2_4922_,
        v_t_4923_,
        v_f_4924_,
        v_a_4925_,
    );
    crate::leanh::lean_dec_ref(v_a_4925_);
    return v_res_4927_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___redArg(
    mut v_inst_4928_: *mut crate::leanh::LeanObject,
    mut v_params_4929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_a_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4931_ =
                    l_Lean_Server_parseRequestParams___redArg(v_inst_4928_, v_params_4929_);
                if crate::leanh::lean_obj_tag(v___x_4931_) == 0 {
                    v_a_4932_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                    v_isSharedCheck_4939_ = (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v___x_4934_ = v___x_4931_;
                        v_isShared_4935_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4932_);
                        crate::leanh::lean_dec(v___x_4931_);
                        v___x_4934_ = crate::leanh::lean_box(0);
                        v_isShared_4935_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4940_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                    v_isSharedCheck_4947_ = (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                    if v_isSharedCheck_4947_ == 0 {
                        v___x_4942_ = v___x_4931_;
                        v_isShared_4943_ = v_isSharedCheck_4947_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4940_);
                        crate::leanh::lean_dec(v___x_4931_);
                        v___x_4942_ = crate::leanh::lean_box(0);
                        v_isShared_4943_ = v_isSharedCheck_4947_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4935_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4934_, 1);
                    v___x_4937_ = v___x_4934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4937_;
            }
            3 => {
                if v_isShared_4943_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4942_, 0);
                    v___x_4945_ = v___x_4942_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
                    v___x_4945_ = v_reuseFailAlloc_4946_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(
    mut v_inst_4948_: *mut crate::leanh::LeanObject,
    mut v_params_4949_: *mut crate::leanh::LeanObject,
    mut v_a_4950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4951_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_4948_, v_params_4949_);
    return v_res_4951_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams(
    mut v_paramType_4952_: *mut crate::leanh::LeanObject,
    mut v_inst_4953_: *mut crate::leanh::LeanObject,
    mut v_params_4954_: *mut crate::leanh::LeanObject,
    mut v_a_4955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4957_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_4953_, v_params_4954_);
    return v___x_4957_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___boxed(
    mut v_paramType_4958_: *mut crate::leanh::LeanObject,
    mut v_inst_4959_: *mut crate::leanh::LeanObject,
    mut v_params_4960_: *mut crate::leanh::LeanObject,
    mut v_a_4961_: *mut crate::leanh::LeanObject,
    mut v_a_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_Lean_Server_RequestM_parseRequestParams(
        v_paramType_4958_,
        v_inst_4959_,
        v_params_4960_,
        v_a_4961_,
    );
    crate::leanh::lean_dec_ref(v_a_4961_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_Server_RequestM_checkCancelled(
    mut v_a_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancelTk_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: u8 = 0;
    v_cancelTk_4966_ = crate::leanh::lean_ctor_get(v_a_4964_, 4);
    v___x_4967_ =
        l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_4966_);
    if v___x_4967_ == 0 {
        let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4968_ = crate::leanh::lean_box(0);
        v___x_4969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4969_, 0, v___x_4968_);
        return v___x_4969_;
    } else {
        let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4970_ = l_Lean_Server_RequestError_requestCancelled;
        v___x_4971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4971_, 0, v___x_4970_);
        return v___x_4971_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_checkCancelled___boxed(
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v_a_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Lean_Server_RequestM_checkCancelled(v_a_4972_);
    crate::leanh::lean_dec_ref(v_a_4972_);
    return v_res_4974_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(
    mut v_inst_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_response_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4981_: u8 = 0;
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_code_4997_: u8 = 0;
    let mut v_message_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4977_) == 0 {
                    v_response_4978_ = crate::leanh::lean_ctor_get(v_x_4977_, 0);
                    v_isSharedCheck_4996_ = (!crate::leanh::lean_is_exclusive(v_x_4977_)) as u8;
                    if v_isSharedCheck_4996_ == 0 {
                        v___x_4980_ = v_x_4977_;
                        v_isShared_4981_ = v_isSharedCheck_4996_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_response_4978_);
                        crate::leanh::lean_dec(v_x_4977_);
                        v___x_4980_ = crate::leanh::lean_box(0);
                        v_isShared_4981_ = v_isSharedCheck_4996_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_4976_);
                    v_code_4997_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_4977_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_message_4998_ = crate::leanh::lean_ctor_get(v_x_4977_, 0);
                    v_isSharedCheck_5005_ = (!crate::leanh::lean_is_exclusive(v_x_4977_)) as u8;
                    if v_isSharedCheck_5005_ == 0 {
                        v___x_5000_ = v_x_4977_;
                        v_isShared_5001_ = v_isSharedCheck_5005_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_message_4998_);
                        crate::leanh::lean_dec(v_x_4977_);
                        v___x_5000_ = crate::leanh::lean_box(0);
                        v_isShared_5001_ = v_isSharedCheck_5005_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_response_4978_);
                v___x_4982_ = crate::leanh::lean_apply_1(v_inst_4976_, v_response_4978_);
                if crate::leanh::lean_obj_tag(v___x_4982_) == 0 {
                    crate::leanh::lean_del_object(v___x_4980_);
                    v_a_4983_ = crate::leanh::lean_ctor_get(v___x_4982_, 0);
                    crate::leanh::lean_inc(v_a_4983_);
                    crate::leanh::lean_dec_ref_known(v___x_4982_, 1);
                    v___x_4984_ = 0;
                    v___x_4985_ =
                        l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0;
                    v___x_4986_ = l_Lean_Json_compress(v_response_4978_);
                    v___x_4987_ = lean_string_append(v___x_4985_, v___x_4986_);
                    crate::leanh::lean_dec_ref(v___x_4986_);
                    v___x_4988_ = l_Lean_Server_parseRequestParams___redArg___closed__1;
                    v___x_4989_ = lean_string_append(v___x_4987_, v___x_4988_);
                    v___x_4990_ = lean_string_append(v___x_4989_, v_a_4983_);
                    crate::leanh::lean_dec(v_a_4983_);
                    v___x_4991_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4991_, 0, v___x_4990_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4991_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4984_,
                    );
                    return v___x_4991_;
                } else {
                    crate::leanh::lean_dec(v_response_4978_);
                    v_a_4992_ = crate::leanh::lean_ctor_get(v___x_4982_, 0);
                    crate::leanh::lean_inc(v_a_4992_);
                    crate::leanh::lean_dec_ref_known(v___x_4982_, 1);
                    if v_isShared_4981_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4980_, 0, v_a_4992_);
                        v___x_4994_ = v___x_4980_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4992_);
                        v___x_4994_ = v_reuseFailAlloc_4995_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4994_;
            }
            3 => {
                if v_isShared_5001_ == 0 {
                    v___x_5003_ = v___x_5000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_message_4998_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5004_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_code_4997_,
                    );
                    v___x_5003_ = v_reuseFailAlloc_5004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___redArg(
    mut v_inst_5006_: *mut crate::leanh::LeanObject,
    mut v_inst_5007_: *mut crate::leanh::LeanObject,
    mut v_method_5008_: *mut crate::leanh::LeanObject,
    mut v_param_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverRequestEmitter_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverRequestEmitter_5012_ = crate::leanh::lean_ctor_get(v_a_5010_, 5);
    v___x_5013_ = crate::leanh::lean_apply_1(v_inst_5006_, v_param_5009_);
    crate::leanh::lean_inc_ref(v_serverRequestEmitter_5012_);
    v___x_5014_ = crate::leanh::lean_apply_3(
        v_serverRequestEmitter_5012_,
        v_method_5008_,
        v___x_5013_,
        crate::leanh::lean_box(0),
    );
    v___f_5015_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5015_, 0, v_inst_5007_);
    v___x_5016_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5015_, v___x_5014_);
    v___x_5017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5017_, 0, v___x_5016_);
    return v___x_5017_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(
    mut v_inst_5018_: *mut crate::leanh::LeanObject,
    mut v_inst_5019_: *mut crate::leanh::LeanObject,
    mut v_method_5020_: *mut crate::leanh::LeanObject,
    mut v_param_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5024_ = l_Lean_Server_RequestM_sendServerRequest___redArg(
        v_inst_5018_,
        v_inst_5019_,
        v_method_5020_,
        v_param_5021_,
        v_a_5022_,
    );
    crate::leanh::lean_dec_ref(v_a_5022_);
    return v_res_5024_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest(
    mut v_paramType_5025_: *mut crate::leanh::LeanObject,
    mut v_inst_5026_: *mut crate::leanh::LeanObject,
    mut v_responseType_5027_: *mut crate::leanh::LeanObject,
    mut v_inst_5028_: *mut crate::leanh::LeanObject,
    mut v_inst_5029_: *mut crate::leanh::LeanObject,
    mut v_method_5030_: *mut crate::leanh::LeanObject,
    mut v_param_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5034_ = l_Lean_Server_RequestM_sendServerRequest___redArg(
        v_inst_5026_,
        v_inst_5028_,
        v_method_5030_,
        v_param_5031_,
        v_a_5032_,
    );
    return v___x_5034_;
}
pub unsafe fn l_Lean_Server_RequestM_sendServerRequest___boxed(
    mut v_paramType_5035_: *mut crate::leanh::LeanObject,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v_responseType_5037_: *mut crate::leanh::LeanObject,
    mut v_inst_5038_: *mut crate::leanh::LeanObject,
    mut v_inst_5039_: *mut crate::leanh::LeanObject,
    mut v_method_5040_: *mut crate::leanh::LeanObject,
    mut v_param_5041_: *mut crate::leanh::LeanObject,
    mut v_a_5042_: *mut crate::leanh::LeanObject,
    mut v_a_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Lean_Server_RequestM_sendServerRequest(
        v_paramType_5035_,
        v_inst_5036_,
        v_responseType_5037_,
        v_inst_5038_,
        v_inst_5039_,
        v_method_5040_,
        v_param_5041_,
        v_a_5042_,
    );
    crate::leanh::lean_dec_ref(v_a_5042_);
    crate::leanh::lean_dec(v_inst_5039_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Server_RequestM_waitFindSnapAux___redArg(
    mut v_notFoundX_5045_: *mut crate::leanh::LeanObject,
    mut v_x_5046_: *mut crate::leanh::LeanObject,
    mut v_x_5047_: *mut crate::leanh::LeanObject,
    mut v_a_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5053_: u8 = 0;
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_a_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5047_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_5046_);
                    crate::leanh::lean_dec_ref(v_notFoundX_5045_);
                    v_a_5050_ = crate::leanh::lean_ctor_get(v_x_5047_, 0);
                    v_isSharedCheck_5058_ = (!crate::leanh::lean_is_exclusive(v_x_5047_)) as u8;
                    if v_isSharedCheck_5058_ == 0 {
                        v___x_5052_ = v_x_5047_;
                        v_isShared_5053_ = v_isSharedCheck_5058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5050_);
                        crate::leanh::lean_dec(v_x_5047_);
                        v___x_5052_ = crate::leanh::lean_box(0);
                        v_isShared_5053_ = v_isSharedCheck_5058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5059_ = crate::leanh::lean_ctor_get(v_x_5047_, 0);
                    crate::leanh::lean_inc(v_a_5059_);
                    crate::leanh::lean_dec_ref_known(v_x_5047_, 1);
                    if crate::leanh::lean_obj_tag(v_a_5059_) == 0 {
                        crate::leanh::lean_dec_ref(v_x_5046_);
                        crate::leanh::lean_inc_ref(v_a_5048_);
                        v___x_5060_ = crate::leanh::lean_apply_2(
                            v_notFoundX_5045_,
                            v_a_5048_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_5060_;
                    } else {
                        crate::leanh::lean_dec_ref(v_notFoundX_5045_);
                        v_val_5061_ = crate::leanh::lean_ctor_get(v_a_5059_, 0);
                        crate::leanh::lean_inc(v_val_5061_);
                        crate::leanh::lean_dec_ref_known(v_a_5059_, 1);
                        crate::leanh::lean_inc_ref(v_a_5048_);
                        v___x_5062_ = crate::leanh::lean_apply_3(
                            v_x_5046_,
                            v_val_5061_,
                            v_a_5048_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_5062_;
                    }
                }
            }
            1 => {
                v___x_5054_ = l_Lean_Server_RequestError_ofIoError(v_a_5050_);
                if v_isShared_5053_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5052_, 1);
                    crate::leanh::lean_ctor_set(v___x_5052_, 0, v___x_5054_);
                    v___x_5056_ = v___x_5052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5054_);
                    v___x_5056_ = v_reuseFailAlloc_5057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(
    mut v_notFoundX_5063_: *mut crate::leanh::LeanObject,
    mut v_x_5064_: *mut crate::leanh::LeanObject,
    mut v_x_5065_: *mut crate::leanh::LeanObject,
    mut v_a_5066_: *mut crate::leanh::LeanObject,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5068_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(
        v_notFoundX_5063_,
        v_x_5064_,
        v_x_5065_,
        v_a_5066_,
    );
    crate::leanh::lean_dec_ref(v_a_5066_);
    return v_res_5068_;
}
pub unsafe fn l_Lean_Server_RequestM_waitFindSnapAux(
    mut v_00_u03b1_5069_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5070_: *mut crate::leanh::LeanObject,
    mut v_x_5071_: *mut crate::leanh::LeanObject,
    mut v_x_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(
        v_notFoundX_5070_,
        v_x_5071_,
        v_x_5072_,
        v_a_5073_,
    );
    return v___x_5075_;
}
pub unsafe fn l_Lean_Server_RequestM_waitFindSnapAux___boxed(
    mut v_00_u03b1_5076_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5077_: *mut crate::leanh::LeanObject,
    mut v_x_5078_: *mut crate::leanh::LeanObject,
    mut v_x_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5082_ = l_Lean_Server_RequestM_waitFindSnapAux(
        v_00_u03b1_5076_,
        v_notFoundX_5077_,
        v_x_5078_,
        v_x_5079_,
        v_a_5080_,
    );
    crate::leanh::lean_dec_ref(v_a_5080_);
    return v_res_5082_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnap___redArg(
    mut v_doc_5083_: *mut crate::leanh::LeanObject,
    mut v_p_5084_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5085_: *mut crate::leanh::LeanObject,
    mut v_x_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_findTask_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_5089_ = crate::leanh::lean_ctor_get(v_doc_5083_, 0);
    crate::leanh::lean_inc_ref(v_toEditableDocumentCore_5089_);
    crate::leanh::lean_dec_ref(v_doc_5083_);
    v_cmdSnaps_5090_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5089_, 2);
    crate::leanh::lean_inc(v_cmdSnaps_5090_);
    crate::leanh::lean_dec_ref(v_toEditableDocumentCore_5089_);
    v_findTask_5091_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_5084_, v_cmdSnaps_5090_);
    v___x_5092_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_waitFindSnapAux___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___x_5092_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5092_, 1, v_notFoundX_5085_);
    crate::leanh::lean_closure_set(v___x_5092_, 2, v_x_5086_);
    v___x_5093_ =
        l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_5091_, v___x_5092_, v_a_5087_);
    return v___x_5093_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(
    mut v_doc_5094_: *mut crate::leanh::LeanObject,
    mut v_p_5095_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5096_: *mut crate::leanh::LeanObject,
    mut v_x_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
    mut v_a_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5100_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(
        v_doc_5094_,
        v_p_5095_,
        v_notFoundX_5096_,
        v_x_5097_,
        v_a_5098_,
    );
    crate::leanh::lean_dec_ref(v_a_5098_);
    return v_res_5100_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnap(
    mut v_00_u03b2_5101_: *mut crate::leanh::LeanObject,
    mut v_doc_5102_: *mut crate::leanh::LeanObject,
    mut v_p_5103_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5104_: *mut crate::leanh::LeanObject,
    mut v_x_5105_: *mut crate::leanh::LeanObject,
    mut v_a_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(
        v_doc_5102_,
        v_p_5103_,
        v_notFoundX_5104_,
        v_x_5105_,
        v_a_5106_,
    );
    return v___x_5108_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnap___boxed(
    mut v_00_u03b2_5109_: *mut crate::leanh::LeanObject,
    mut v_doc_5110_: *mut crate::leanh::LeanObject,
    mut v_p_5111_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5112_: *mut crate::leanh::LeanObject,
    mut v_x_5113_: *mut crate::leanh::LeanObject,
    mut v_a_5114_: *mut crate::leanh::LeanObject,
    mut v_a_5115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5116_ = l_Lean_Server_RequestM_withWaitFindSnap(
        v_00_u03b2_5109_,
        v_doc_5110_,
        v_p_5111_,
        v_notFoundX_5112_,
        v_x_5113_,
        v_a_5114_,
    );
    crate::leanh::lean_dec_ref(v_a_5114_);
    return v_res_5116_;
}
pub unsafe fn l_Lean_Server_RequestM_bindWaitFindSnap___redArg(
    mut v_doc_5117_: *mut crate::leanh::LeanObject,
    mut v_p_5118_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5119_: *mut crate::leanh::LeanObject,
    mut v_x_5120_: *mut crate::leanh::LeanObject,
    mut v_a_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdSnaps_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_findTask_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_5123_ = crate::leanh::lean_ctor_get(v_doc_5117_, 0);
    crate::leanh::lean_inc_ref(v_toEditableDocumentCore_5123_);
    crate::leanh::lean_dec_ref(v_doc_5117_);
    v_cmdSnaps_5124_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5123_, 2);
    crate::leanh::lean_inc(v_cmdSnaps_5124_);
    crate::leanh::lean_dec_ref(v_toEditableDocumentCore_5123_);
    v_findTask_5125_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_5118_, v_cmdSnaps_5124_);
    v___x_5126_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_waitFindSnapAux___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___x_5126_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5126_, 1, v_notFoundX_5119_);
    crate::leanh::lean_closure_set(v___x_5126_, 2, v_x_5120_);
    v___x_5127_ =
        l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_5125_, v___x_5126_, v_a_5121_);
    return v___x_5127_;
}
pub unsafe fn l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(
    mut v_doc_5128_: *mut crate::leanh::LeanObject,
    mut v_p_5129_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5130_: *mut crate::leanh::LeanObject,
    mut v_x_5131_: *mut crate::leanh::LeanObject,
    mut v_a_5132_: *mut crate::leanh::LeanObject,
    mut v_a_5133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5134_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(
        v_doc_5128_,
        v_p_5129_,
        v_notFoundX_5130_,
        v_x_5131_,
        v_a_5132_,
    );
    crate::leanh::lean_dec_ref(v_a_5132_);
    return v_res_5134_;
}
pub unsafe fn l_Lean_Server_RequestM_bindWaitFindSnap(
    mut v_00_u03b2_5135_: *mut crate::leanh::LeanObject,
    mut v_doc_5136_: *mut crate::leanh::LeanObject,
    mut v_p_5137_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5138_: *mut crate::leanh::LeanObject,
    mut v_x_5139_: *mut crate::leanh::LeanObject,
    mut v_a_5140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5142_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(
        v_doc_5136_,
        v_p_5137_,
        v_notFoundX_5138_,
        v_x_5139_,
        v_a_5140_,
    );
    return v___x_5142_;
}
pub unsafe fn l_Lean_Server_RequestM_bindWaitFindSnap___boxed(
    mut v_00_u03b2_5143_: *mut crate::leanh::LeanObject,
    mut v_doc_5144_: *mut crate::leanh::LeanObject,
    mut v_p_5145_: *mut crate::leanh::LeanObject,
    mut v_notFoundX_5146_: *mut crate::leanh::LeanObject,
    mut v_x_5147_: *mut crate::leanh::LeanObject,
    mut v_a_5148_: *mut crate::leanh::LeanObject,
    mut v_a_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ = l_Lean_Server_RequestM_bindWaitFindSnap(
        v_00_u03b2_5143_,
        v_doc_5144_,
        v_p_5145_,
        v_notFoundX_5146_,
        v_x_5147_,
        v_a_5148_,
    );
    crate::leanh::lean_dec_ref(v_a_5148_);
    return v_res_5150_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(
    mut v___y_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_doc_5153_ = crate::leanh::lean_ctor_get(v___y_5151_, 1);
    crate::leanh::lean_inc_ref(v_doc_5153_);
    v___x_5154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5154_, 0, v_doc_5153_);
    return v___x_5154_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(
            v___y_5155_,
        );
    crate::leanh::lean_dec_ref(v___y_5155_);
    return v_res_5157_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(
    mut v___x_5158_: *mut crate::leanh::LeanObject,
    mut v_s_5159_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    v___x_5160_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_5159_);
    v___x_5161_ = lean_nat_dec_le(v___x_5158_, v___x_5160_);
    crate::leanh::lean_dec(v___x_5160_);
    return v___x_5161_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(
    mut v___x_5162_: *mut crate::leanh::LeanObject,
    mut v_s_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5164_: u8 = 0;
    let mut v_r_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ =
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_5162_, v_s_5163_);
    crate::leanh::lean_dec_ref(v_s_5163_);
    crate::leanh::lean_dec(v___x_5162_);
    v_r_5165_ = crate::leanh::lean_box((v_res_5164_) as usize);
    return v_r_5165_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(
    mut v___x_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5169_, 0, v___x_5166_);
    return v___x_5169_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(
    mut v___x_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5173_ =
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_5170_, v___y_5171_);
    crate::leanh::lean_dec_ref(v___y_5171_);
    return v_res_5173_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(
    mut v_lspPos_5178_: *mut crate::leanh::LeanObject,
    mut v_f_5179_: *mut crate::leanh::LeanObject,
    mut v_a_5180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5182_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(
            v_a_5180_,
        );
    v_a_5183_ = crate::leanh::lean_ctor_get(v___x_5182_, 0);
    crate::leanh::lean_inc(v_a_5183_);
    crate::leanh::lean_dec_ref(v___x_5182_);
    v_toEditableDocumentCore_5184_ = crate::leanh::lean_ctor_get(v_a_5183_, 0);
    v_meta_5185_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5184_, 0);
    v_text_5186_ = crate::leanh::lean_ctor_get(v_meta_5185_, 3);
    v_line_5187_ = crate::leanh::lean_ctor_get(v_lspPos_5178_, 0);
    crate::leanh::lean_inc(v_line_5187_);
    v_character_5188_ = crate::leanh::lean_ctor_get(v_lspPos_5178_, 1);
    crate::leanh::lean_inc(v_character_5188_);
    v___x_5189_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_5186_, v_lspPos_5178_);
    v___f_5190_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5190_, 0, v___x_5189_);
    v___x_5191_ = 3;
    v___x_5192_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0;
    v___x_5193_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1;
    v___x_5194_ = l_Nat_reprFast(v_line_5187_);
    v___x_5195_ = lean_string_append(v___x_5193_, v___x_5194_);
    crate::leanh::lean_dec_ref(v___x_5194_);
    v___x_5196_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2;
    v___x_5197_ = lean_string_append(v___x_5195_, v___x_5196_);
    v___x_5198_ = l_Nat_reprFast(v_character_5188_);
    v___x_5199_ = lean_string_append(v___x_5197_, v___x_5198_);
    crate::leanh::lean_dec_ref(v___x_5198_);
    v___x_5200_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3;
    v___x_5201_ = lean_string_append(v___x_5199_, v___x_5200_);
    v___x_5202_ = lean_string_append(v___x_5192_, v___x_5201_);
    crate::leanh::lean_dec_ref(v___x_5201_);
    v___x_5203_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5203_, 0, v___x_5202_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5203_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5191_,
    );
    v___f_5204_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5204_, 0, v___x_5203_);
    v___x_5205_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(
        v_a_5183_,
        v___f_5190_,
        v___f_5204_,
        v_f_5179_,
        v_a_5180_,
    );
    return v___x_5205_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(
    mut v_lspPos_5206_: *mut crate::leanh::LeanObject,
    mut v_f_5207_: *mut crate::leanh::LeanObject,
    mut v_a_5208_: *mut crate::leanh::LeanObject,
    mut v_a_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5210_ =
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_5206_, v_f_5207_, v_a_5208_);
    crate::leanh::lean_dec_ref(v_a_5208_);
    return v_res_5210_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos(
    mut v_00_u03b1_5211_: *mut crate::leanh::LeanObject,
    mut v_lspPos_5212_: *mut crate::leanh::LeanObject,
    mut v_f_5213_: *mut crate::leanh::LeanObject,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5216_ =
        l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_5212_, v_f_5213_, v_a_5214_);
    return v___x_5216_;
}
pub unsafe fn l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(
    mut v_00_u03b1_5217_: *mut crate::leanh::LeanObject,
    mut v_lspPos_5218_: *mut crate::leanh::LeanObject,
    mut v_f_5219_: *mut crate::leanh::LeanObject,
    mut v_a_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(
        v_00_u03b1_5217_,
        v_lspPos_5218_,
        v_f_5219_,
        v_a_5220_,
    );
    crate::leanh::lean_dec_ref(v_a_5220_);
    return v_res_5222_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(
    mut v_hoverPos_5223_: *mut crate::leanh::LeanObject,
    mut v_cmdParsed_5224_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_stx_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stx_5225_ = crate::leanh::lean_ctor_get(v_cmdParsed_5224_, 1);
    v___x_5226_ = 1;
    v___x_5227_ = l_Lean_Syntax_getPos_x3f(v_stx_5225_, v___x_5226_);
    if crate::leanh::lean_obj_tag(v___x_5227_) == 1 {
        let mut v_val_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5229_: u8 = 0;
        v_val_5228_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
        crate::leanh::lean_inc(v_val_5228_);
        crate::leanh::lean_dec_ref_known(v___x_5227_, 1);
        v___x_5229_ = lean_nat_dec_lt(v_hoverPos_5223_, v_val_5228_);
        crate::leanh::lean_dec(v_val_5228_);
        return v___x_5229_;
    } else {
        let mut v___x_5230_: u8 = 0;
        crate::leanh::lean_dec(v___x_5227_);
        v___x_5230_ = 0;
        return v___x_5230_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(
    mut v_hoverPos_5231_: *mut crate::leanh::LeanObject,
    mut v_cmdParsed_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5233_: u8 = 0;
    let mut v_r_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5233_ =
        l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(
            v_hoverPos_5231_,
            v_cmdParsed_5232_,
        );
    crate::leanh::lean_dec_ref(v_cmdParsed_5232_);
    crate::leanh::lean_dec(v_hoverPos_5231_);
    v_r_5234_ = crate::leanh::lean_box((v_res_5233_) as usize);
    return v_r_5234_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(
    mut v_doc_5235_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5236_: *mut crate::leanh::LeanObject,
    mut v_cmdParsed_5237_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_stx_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stx_5238_ = crate::leanh::lean_ctor_get(v_cmdParsed_5237_, 1);
    v___x_5239_ = 1;
    v___x_5240_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_5238_, v___x_5239_);
    if crate::leanh::lean_obj_tag(v___x_5240_) == 1 {
        let mut v_toEditableDocumentCore_5241_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v_meta_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5245_: u8 = 0;
        let mut v___x_5246_: u8 = 0;
        v_toEditableDocumentCore_5241_ = crate::leanh::lean_ctor_get(v_doc_5235_, 0);
        v_meta_5242_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5241_, 0);
        v_val_5243_ = crate::leanh::lean_ctor_get(v___x_5240_, 0);
        crate::leanh::lean_inc(v_val_5243_);
        crate::leanh::lean_dec_ref_known(v___x_5240_, 1);
        v_text_5244_ = crate::leanh::lean_ctor_get(v_meta_5242_, 3);
        v___x_5245_ = 0;
        v___x_5246_ = l_Lean_FileMap_rangeContainsHoverPos(
            v_text_5244_,
            v_val_5243_,
            v_hoverPos_5236_,
            v___x_5245_,
        );
        crate::leanh::lean_dec(v_val_5243_);
        return v___x_5246_;
    } else {
        let mut v___x_5247_: u8 = 0;
        crate::leanh::lean_dec(v___x_5240_);
        v___x_5247_ = 0;
        return v___x_5247_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(
    mut v_doc_5248_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5249_: *mut crate::leanh::LeanObject,
    mut v_cmdParsed_5250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5251_: u8 = 0;
    let mut v_r_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5251_ =
        l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(
            v_doc_5248_,
            v_hoverPos_5249_,
            v_cmdParsed_5250_,
        );
    crate::leanh::lean_dec_ref(v_cmdParsed_5250_);
    crate::leanh::lean_dec(v_hoverPos_5249_);
    crate::leanh::lean_dec_ref(v_doc_5248_);
    v_r_5252_ = crate::leanh::lean_box((v_res_5251_) as usize);
    return v_r_5252_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5253_ = crate::leanh::lean_box(0);
    v___x_5254_ = lean_task_pure(v___x_5253_);
    return v___x_5254_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go(
    mut v_doc_5255_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5256_: *mut crate::leanh::LeanObject,
    mut v_cmdParsed_5257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5258_: u8 = 0;
    v___x_5258_ =
        l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(
            v_doc_5255_,
            v_hoverPos_5256_,
            v_cmdParsed_5257_,
        );
    if v___x_5258_ == 0 {
        let mut v___x_5259_: u8 = 0;
        v___x_5259_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_5256_, v_cmdParsed_5257_);
        if v___x_5259_ == 0 {
            let mut v_nextCmdSnap_x3f_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_nextCmdSnap_x3f_5260_ = crate::leanh::lean_ctor_get(v_cmdParsed_5257_, 4);
            crate::leanh::lean_inc(v_nextCmdSnap_x3f_5260_);
            crate::leanh::lean_dec_ref(v_cmdParsed_5257_);
            if crate::leanh::lean_obj_tag(v_nextCmdSnap_x3f_5260_) == 0 {
                let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_hoverPos_5256_);
                crate::leanh::lean_dec_ref(v_doc_5255_);
                v___x_5261_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
                return v___x_5261_;
            } else {
                let mut v_val_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_task_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_5262_ = crate::leanh::lean_ctor_get(v_nextCmdSnap_x3f_5260_, 0);
                crate::leanh::lean_inc(v_val_5262_);
                crate::leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_5260_, 1);
                v_task_5263_ = crate::leanh::lean_ctor_get(v_val_5262_, 3);
                crate::leanh::lean_inc_ref(v_task_5263_);
                crate::leanh::lean_dec(v_val_5262_);
                v___x_5264_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_5264_, 0, v_doc_5255_);
                crate::leanh::lean_closure_set(v___x_5264_, 1, v_hoverPos_5256_);
                v___x_5265_ =
                    l_Lean_Server_ServerTask_bindCheap___redArg(v_task_5263_, v___x_5264_);
                return v___x_5265_;
            }
        } else {
            let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_cmdParsed_5257_);
            crate::leanh::lean_dec(v_hoverPos_5256_);
            crate::leanh::lean_dec_ref(v_doc_5255_);
            v___x_5266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
            return v___x_5266_;
        }
    } else {
        let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hoverPos_5256_);
        crate::leanh::lean_dec_ref(v_doc_5255_);
        v___x_5267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5267_, 0, v_cmdParsed_5257_);
        v___x_5268_ = lean_task_pure(v___x_5267_);
        return v___x_5268_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_findCmdParsedSnap___lam__0(
    mut v_doc_5269_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5270_: *mut crate::leanh::LeanObject,
    mut v_headerProcessed_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_x3f_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_x3f_5272_ = crate::leanh::lean_ctor_get(v_headerProcessed_5271_, 2);
    crate::leanh::lean_inc(v_result_x3f_5272_);
    crate::leanh::lean_dec_ref(v_headerProcessed_5271_);
    if crate::leanh::lean_obj_tag(v_result_x3f_5272_) == 1 {
        let mut v_val_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_firstCmdSnap_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_task_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5273_ = crate::leanh::lean_ctor_get(v_result_x3f_5272_, 0);
        crate::leanh::lean_inc(v_val_5273_);
        crate::leanh::lean_dec_ref_known(v_result_x3f_5272_, 1);
        v_firstCmdSnap_5274_ = crate::leanh::lean_ctor_get(v_val_5273_, 1);
        crate::leanh::lean_inc_ref(v_firstCmdSnap_5274_);
        crate::leanh::lean_dec(v_val_5273_);
        v_task_5275_ = crate::leanh::lean_ctor_get(v_firstCmdSnap_5274_, 3);
        crate::leanh::lean_inc_ref(v_task_5275_);
        crate::leanh::lean_dec_ref(v_firstCmdSnap_5274_);
        v___x_5276_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go
                as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___x_5276_, 0, v_doc_5269_);
        crate::leanh::lean_closure_set(v___x_5276_, 1, v_hoverPos_5270_);
        v___x_5277_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_5275_, v___x_5276_);
        return v___x_5277_;
    } else {
        let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_result_x3f_5272_);
        crate::leanh::lean_dec(v_hoverPos_5270_);
        crate::leanh::lean_dec_ref(v_doc_5269_);
        v___x_5278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
        return v___x_5278_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_findCmdParsedSnap(
    mut v_doc_5279_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEditableDocumentCore_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSnap_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEditableDocumentCore_5281_ = crate::leanh::lean_ctor_get(v_doc_5279_, 0);
    v_initSnap_5282_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5281_, 1);
    v_result_x3f_5283_ = crate::leanh::lean_ctor_get(v_initSnap_5282_, 4);
    if crate::leanh::lean_obj_tag(v_result_x3f_5283_) == 1 {
        let mut v_val_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_processedSnap_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_task_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5284_ = crate::leanh::lean_ctor_get(v_result_x3f_5283_, 0);
        v_processedSnap_5285_ = crate::leanh::lean_ctor_get(v_val_5284_, 1);
        v_task_5286_ = crate::leanh::lean_ctor_get(v_processedSnap_5285_, 3);
        crate::leanh::lean_inc_ref(v_task_5286_);
        v___f_5287_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_RequestM_findCmdParsedSnap___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5287_, 0, v_doc_5279_);
        crate::leanh::lean_closure_set(v___f_5287_, 1, v_hoverPos_5280_);
        v___x_5288_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_5286_, v___f_5287_);
        return v___x_5288_;
    } else {
        let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hoverPos_5280_);
        crate::leanh::lean_dec_ref(v_doc_5279_);
        v___x_5289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
        return v___x_5289_;
    }
}
pub unsafe fn l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(
    mut v_msg_5290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5291_ = crate::leanh::lean_box(0);
    v___x_5292_ = lean_panic_fn_borrowed(v___x_5291_, v_msg_5290_);
    return v___x_5292_;
}
pub unsafe fn _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2;
    v___x_5297_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_5298_ = crate::leanh::lean_unsigned_to_nat(418);
    v___x_5299_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1;
    v___x_5300_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0;
    v___x_5301_ = l_mkPanicMessageWithDecl(
        v___x_5300_,
        v___x_5299_,
        v___x_5298_,
        v___x_5297_,
        v___x_5296_,
    );
    return v___x_5301_;
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos___lam__0(
    mut v_stx_5302_: *mut crate::leanh::LeanObject,
    mut v_s_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_infoTree_x3f_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5310_: u8 = 0;
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_infoTree_x3f_5304_ = crate::leanh::lean_ctor_get(v_s_5303_, 2);
                crate::leanh::lean_inc(v_infoTree_x3f_5304_);
                crate::leanh::lean_dec_ref(v_s_5303_);
                if crate::leanh::lean_obj_tag(v_infoTree_x3f_5304_) == 0 {
                    crate::leanh::lean_dec(v_stx_5302_);
                    v___x_5305_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3,
                    );
                    v___x_5306_ =
                        l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(v___x_5305_);
                    return v___x_5306_;
                } else {
                    v_val_5307_ = crate::leanh::lean_ctor_get(v_infoTree_x3f_5304_, 0);
                    v_isSharedCheck_5315_ =
                        (!crate::leanh::lean_is_exclusive(v_infoTree_x3f_5304_)) as u8;
                    if v_isSharedCheck_5315_ == 0 {
                        v___x_5309_ = v_infoTree_x3f_5304_;
                        v_isShared_5310_ = v_isSharedCheck_5315_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5307_);
                        crate::leanh::lean_dec(v_infoTree_x3f_5304_);
                        v___x_5309_ = crate::leanh::lean_box(0);
                        v_isShared_5310_ = v_isSharedCheck_5315_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5311_, 0, v_stx_5302_);
                crate::leanh::lean_ctor_set(v___x_5311_, 1, v_val_5307_);
                if v_isShared_5310_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5309_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos___lam__1(
    mut v_elabSnap_5316_: *mut crate::leanh::LeanObject,
    mut v___f_5317_: *mut crate::leanh::LeanObject,
    mut v_stx_5318_: *mut crate::leanh::LeanObject,
    mut v_x_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_infoTreeSnap_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5319_) == 0 {
                    crate::leanh::lean_dec(v_stx_5318_);
                    v_infoTreeSnap_5320_ = crate::leanh::lean_ctor_get(v_elabSnap_5316_, 3);
                    crate::leanh::lean_inc_ref(v_infoTreeSnap_5320_);
                    crate::leanh::lean_dec_ref(v_elabSnap_5316_);
                    v_task_5321_ = crate::leanh::lean_ctor_get(v_infoTreeSnap_5320_, 3);
                    crate::leanh::lean_inc_ref(v_task_5321_);
                    crate::leanh::lean_dec_ref(v_infoTreeSnap_5320_);
                    v___x_5322_ =
                        l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5317_, v_task_5321_);
                    return v___x_5322_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_5317_);
                    crate::leanh::lean_dec_ref(v_elabSnap_5316_);
                    v_val_5323_ = crate::leanh::lean_ctor_get(v_x_5319_, 0);
                    v_isSharedCheck_5332_ = (!crate::leanh::lean_is_exclusive(v_x_5319_)) as u8;
                    if v_isSharedCheck_5332_ == 0 {
                        v___x_5325_ = v_x_5319_;
                        v_isShared_5326_ = v_isSharedCheck_5332_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5323_);
                        crate::leanh::lean_dec(v_x_5319_);
                        v___x_5325_ = crate::leanh::lean_box(0);
                        v_isShared_5326_ = v_isSharedCheck_5332_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5327_, 0, v_stx_5318_);
                crate::leanh::lean_ctor_set(v___x_5327_, 1, v_val_5323_);
                if v_isShared_5326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5325_, 0, v___x_5327_);
                    v___x_5329_ = v___x_5325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5327_);
                    v___x_5329_ = v_reuseFailAlloc_5331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5330_ = lean_task_pure(v___x_5329_);
                return v___x_5330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5333_ = crate::leanh::lean_box(0);
    v___x_5334_ = lean_task_pure(v___x_5333_);
    return v___x_5334_;
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(
    mut v_doc_5335_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5336_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5337_: u8,
    mut v_x_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5338_) == 0 {
        let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hoverPos_5336_);
        crate::leanh::lean_dec_ref(v_doc_5335_);
        v___x_5339_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once
            ),
            _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0,
        );
        return v___x_5339_;
    } else {
        let mut v_toEditableDocumentCore_5340_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v_meta_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_elabSnap_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toEditableDocumentCore_5340_ = crate::leanh::lean_ctor_get(v_doc_5335_, 0);
        crate::leanh::lean_inc_ref(v_toEditableDocumentCore_5340_);
        crate::leanh::lean_dec_ref(v_doc_5335_);
        v_meta_5341_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5340_, 0);
        crate::leanh::lean_inc_ref(v_meta_5341_);
        crate::leanh::lean_dec_ref(v_toEditableDocumentCore_5340_);
        v_val_5342_ = crate::leanh::lean_ctor_get(v_x_5338_, 0);
        crate::leanh::lean_inc(v_val_5342_);
        crate::leanh::lean_dec_ref_known(v_x_5338_, 1);
        v_text_5343_ = crate::leanh::lean_ctor_get(v_meta_5341_, 3);
        crate::leanh::lean_inc_ref(v_text_5343_);
        crate::leanh::lean_dec_ref(v_meta_5341_);
        v_stx_5344_ = crate::leanh::lean_ctor_get(v_val_5342_, 1);
        crate::leanh::lean_inc_n(v_stx_5344_, 2);
        v_elabSnap_5345_ = crate::leanh::lean_ctor_get(v_val_5342_, 3);
        crate::leanh::lean_inc_ref_n(v_elabSnap_5345_, 2);
        crate::leanh::lean_dec(v_val_5342_);
        v___f_5346_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_RequestM_findCmdDataAtPos___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5346_, 0, v_stx_5344_);
        v___f_5347_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_RequestM_findCmdDataAtPos___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_5347_, 0, v_elabSnap_5345_);
        crate::leanh::lean_closure_set(v___f_5347_, 1, v___f_5346_);
        crate::leanh::lean_closure_set(v___f_5347_, 2, v_stx_5344_);
        v___x_5348_ =
            l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(v_elabSnap_5345_);
        v___x_5349_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(
            v_text_5343_,
            v___x_5348_,
            v_hoverPos_5336_,
            v_includeStop_5337_,
        );
        v___x_5350_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_5349_, v___f_5347_);
        return v___x_5350_;
    }
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed(
    mut v_doc_5351_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5352_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5353_: *mut crate::leanh::LeanObject,
    mut v_x_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_5355_: u8 = 0;
    let mut v_res_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5355_ = (crate::leanh::lean_unbox(v_includeStop_5353_) as u8);
    v_res_5356_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(
        v_doc_5351_,
        v_hoverPos_5352_,
        v_includeStop_boxed_5355_,
        v_x_5354_,
    );
    return v_res_5356_;
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos(
    mut v_doc_5357_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5358_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5359_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = crate::leanh::lean_box((v_includeStop_5359_) as usize);
    crate::leanh::lean_inc(v_hoverPos_5358_);
    crate::leanh::lean_inc_ref(v_doc_5357_);
    v___f_5361_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5361_, 0, v_doc_5357_);
    crate::leanh::lean_closure_set(v___f_5361_, 1, v_hoverPos_5358_);
    crate::leanh::lean_closure_set(v___f_5361_, 2, v___x_5360_);
    v___x_5362_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_5357_, v_hoverPos_5358_);
    v___x_5363_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_5362_, v___f_5361_);
    return v___x_5363_;
}
pub unsafe fn l_Lean_Server_RequestM_findCmdDataAtPos___boxed(
    mut v_doc_5364_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5365_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_5367_: u8 = 0;
    let mut v_res_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5367_ = (crate::leanh::lean_unbox(v_includeStop_5366_) as u8);
    v_res_5368_ = l_Lean_Server_RequestM_findCmdDataAtPos(
        v_doc_5364_,
        v_hoverPos_5365_,
        v_includeStop_boxed_5367_,
    );
    return v_res_5368_;
}
pub unsafe fn l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0(
    mut v_x_5369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5374_: u8 = 0;
    let mut v_snd_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5369_) == 0 {
                    v___x_5370_ = crate::leanh::lean_box(0);
                    return v___x_5370_;
                } else {
                    v_val_5371_ = crate::leanh::lean_ctor_get(v_x_5369_, 0);
                    v_isSharedCheck_5379_ = (!crate::leanh::lean_is_exclusive(v_x_5369_)) as u8;
                    if v_isSharedCheck_5379_ == 0 {
                        v___x_5373_ = v_x_5369_;
                        v_isShared_5374_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5371_);
                        crate::leanh::lean_dec(v_x_5369_);
                        v___x_5373_ = crate::leanh::lean_box(0);
                        v_isShared_5374_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5375_ = crate::leanh::lean_ctor_get(v_val_5371_, 1);
                crate::leanh::lean_inc(v_snd_5375_);
                crate::leanh::lean_dec(v_val_5371_);
                if v_isShared_5374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5373_, 0, v_snd_5375_);
                    v___x_5377_ = v___x_5373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_snd_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_findInfoTreeAtPos(
    mut v_doc_5381_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5382_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5383_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5384_ = l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0;
    v___x_5385_ =
        l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_5381_, v_hoverPos_5382_, v_includeStop_5383_);
    v___x_5386_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5384_, v___x_5385_);
    return v___x_5386_;
}
pub unsafe fn l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(
    mut v_doc_5387_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_5388_: *mut crate::leanh::LeanObject,
    mut v_includeStop_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_5390_: u8 = 0;
    let mut v_res_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_5390_ = (crate::leanh::lean_unbox(v_includeStop_5389_) as u8);
    v_res_5391_ = l_Lean_Server_RequestM_findInfoTreeAtPos(
        v_doc_5387_,
        v_hoverPos_5388_,
        v_includeStop_boxed_5390_,
    );
    return v_res_5391_;
}
pub unsafe fn l_Lean_Server_RequestM_runCommandElabM___redArg(
    mut v_snap_5392_: *mut crate::leanh::LeanObject,
    mut v_c_5393_: *mut crate::leanh::LeanObject,
    mut v_a_5394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_a_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v_a_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5396_ = crate::leanh::lean_ctor_get(v_a_5394_, 1);
                v_toEditableDocumentCore_5397_ = crate::leanh::lean_ctor_get(v_doc_5396_, 0);
                v_meta_5398_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5397_, 0);
                crate::leanh::lean_inc_ref(v_a_5394_);
                v___x_5399_ = crate::leanh::lean_apply_1(v_c_5393_, v_a_5394_);
                v___x_5400_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
                    v_snap_5392_,
                    v_meta_5398_,
                    v___x_5399_,
                );
                if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                    v_a_5401_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5413_ = (!crate::leanh::lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5413_ == 0 {
                        v___x_5403_ = v___x_5400_;
                        v_isShared_5404_ = v_isSharedCheck_5413_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5401_);
                        crate::leanh::lean_dec(v___x_5400_);
                        v___x_5403_ = crate::leanh::lean_box(0);
                        v_isShared_5404_ = v_isSharedCheck_5413_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5414_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                    crate::leanh::lean_inc(v_a_5414_);
                    crate::leanh::lean_dec_ref_known(v___x_5400_, 1);
                    v___x_5415_ = l_Lean_Server_RequestError_ofException(v_a_5414_);
                    v_a_5416_ = crate::leanh::lean_ctor_get(v___x_5415_, 0);
                    v_isSharedCheck_5423_ = (!crate::leanh::lean_is_exclusive(v___x_5415_)) as u8;
                    if v_isSharedCheck_5423_ == 0 {
                        v___x_5418_ = v___x_5415_;
                        v_isShared_5419_ = v_isSharedCheck_5423_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5416_);
                        crate::leanh::lean_dec(v___x_5415_);
                        v___x_5418_ = crate::leanh::lean_box(0);
                        v_isShared_5419_ = v_isSharedCheck_5423_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5401_) == 0 {
                    v_a_5405_ = crate::leanh::lean_ctor_get(v_a_5401_, 0);
                    crate::leanh::lean_inc(v_a_5405_);
                    crate::leanh::lean_dec_ref_known(v_a_5401_, 1);
                    if v_isShared_5404_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5403_, 1);
                        crate::leanh::lean_ctor_set(v___x_5403_, 0, v_a_5405_);
                        v___x_5407_ = v___x_5403_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5408_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5405_);
                        v___x_5407_ = v_reuseFailAlloc_5408_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5409_ = crate::leanh::lean_ctor_get(v_a_5401_, 0);
                    crate::leanh::lean_inc(v_a_5409_);
                    crate::leanh::lean_dec_ref_known(v_a_5401_, 1);
                    if v_isShared_5404_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5403_, 0, v_a_5409_);
                        v___x_5411_ = v___x_5403_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5409_);
                        v___x_5411_ = v_reuseFailAlloc_5412_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5407_;
            }
            3 => {
                return v___x_5411_;
            }
            4 => {
                if v_isShared_5419_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5418_, 1);
                    v___x_5421_ = v___x_5418_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
                    v___x_5421_ = v_reuseFailAlloc_5422_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(
    mut v_snap_5424_: *mut crate::leanh::LeanObject,
    mut v_c_5425_: *mut crate::leanh::LeanObject,
    mut v_a_5426_: *mut crate::leanh::LeanObject,
    mut v_a_5427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5428_ =
        l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_5424_, v_c_5425_, v_a_5426_);
    crate::leanh::lean_dec_ref(v_a_5426_);
    return v_res_5428_;
}
pub unsafe fn l_Lean_Server_RequestM_runCommandElabM(
    mut v_00_u03b1_5429_: *mut crate::leanh::LeanObject,
    mut v_snap_5430_: *mut crate::leanh::LeanObject,
    mut v_c_5431_: *mut crate::leanh::LeanObject,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5434_ =
        l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_5430_, v_c_5431_, v_a_5432_);
    return v___x_5434_;
}
pub unsafe fn l_Lean_Server_RequestM_runCommandElabM___boxed(
    mut v_00_u03b1_5435_: *mut crate::leanh::LeanObject,
    mut v_snap_5436_: *mut crate::leanh::LeanObject,
    mut v_c_5437_: *mut crate::leanh::LeanObject,
    mut v_a_5438_: *mut crate::leanh::LeanObject,
    mut v_a_5439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5440_ = l_Lean_Server_RequestM_runCommandElabM(
        v_00_u03b1_5435_,
        v_snap_5436_,
        v_c_5437_,
        v_a_5438_,
    );
    crate::leanh::lean_dec_ref(v_a_5438_);
    return v_res_5440_;
}
pub unsafe fn l_Lean_Server_RequestM_runCoreM___redArg(
    mut v_snap_5441_: *mut crate::leanh::LeanObject,
    mut v_c_5442_: *mut crate::leanh::LeanObject,
    mut v_a_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5453_: u8 = 0;
    let mut v_a_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5462_: u8 = 0;
    let mut v_a_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5468_: u8 = 0;
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5445_ = crate::leanh::lean_ctor_get(v_a_5443_, 1);
                v_toEditableDocumentCore_5446_ = crate::leanh::lean_ctor_get(v_doc_5445_, 0);
                v_meta_5447_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5446_, 0);
                crate::leanh::lean_inc_ref(v_a_5443_);
                v___x_5448_ = crate::leanh::lean_apply_1(v_c_5442_, v_a_5443_);
                v___x_5449_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(
                    v_snap_5441_,
                    v_meta_5447_,
                    v___x_5448_,
                );
                if crate::leanh::lean_obj_tag(v___x_5449_) == 0 {
                    v_a_5450_ = crate::leanh::lean_ctor_get(v___x_5449_, 0);
                    v_isSharedCheck_5462_ = (!crate::leanh::lean_is_exclusive(v___x_5449_)) as u8;
                    if v_isSharedCheck_5462_ == 0 {
                        v___x_5452_ = v___x_5449_;
                        v_isShared_5453_ = v_isSharedCheck_5462_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5450_);
                        crate::leanh::lean_dec(v___x_5449_);
                        v___x_5452_ = crate::leanh::lean_box(0);
                        v_isShared_5453_ = v_isSharedCheck_5462_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5463_ = crate::leanh::lean_ctor_get(v___x_5449_, 0);
                    crate::leanh::lean_inc(v_a_5463_);
                    crate::leanh::lean_dec_ref_known(v___x_5449_, 1);
                    v___x_5464_ = l_Lean_Server_RequestError_ofException(v_a_5463_);
                    v_a_5465_ = crate::leanh::lean_ctor_get(v___x_5464_, 0);
                    v_isSharedCheck_5472_ = (!crate::leanh::lean_is_exclusive(v___x_5464_)) as u8;
                    if v_isSharedCheck_5472_ == 0 {
                        v___x_5467_ = v___x_5464_;
                        v_isShared_5468_ = v_isSharedCheck_5472_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5465_);
                        crate::leanh::lean_dec(v___x_5464_);
                        v___x_5467_ = crate::leanh::lean_box(0);
                        v_isShared_5468_ = v_isSharedCheck_5472_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5450_) == 0 {
                    v_a_5454_ = crate::leanh::lean_ctor_get(v_a_5450_, 0);
                    crate::leanh::lean_inc(v_a_5454_);
                    crate::leanh::lean_dec_ref_known(v_a_5450_, 1);
                    if v_isShared_5453_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5452_, 1);
                        crate::leanh::lean_ctor_set(v___x_5452_, 0, v_a_5454_);
                        v___x_5456_ = v___x_5452_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5454_);
                        v___x_5456_ = v_reuseFailAlloc_5457_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5458_ = crate::leanh::lean_ctor_get(v_a_5450_, 0);
                    crate::leanh::lean_inc(v_a_5458_);
                    crate::leanh::lean_dec_ref_known(v_a_5450_, 1);
                    if v_isShared_5453_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5452_, 0, v_a_5458_);
                        v___x_5460_ = v___x_5452_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5458_);
                        v___x_5460_ = v_reuseFailAlloc_5461_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5456_;
            }
            3 => {
                return v___x_5460_;
            }
            4 => {
                if v_isShared_5468_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5467_, 1);
                    v___x_5470_ = v___x_5467_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5465_);
                    v___x_5470_ = v_reuseFailAlloc_5471_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_runCoreM___redArg___boxed(
    mut v_snap_5473_: *mut crate::leanh::LeanObject,
    mut v_c_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_5473_, v_c_5474_, v_a_5475_);
    crate::leanh::lean_dec_ref(v_a_5475_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_Server_RequestM_runCoreM(
    mut v_00_u03b1_5478_: *mut crate::leanh::LeanObject,
    mut v_snap_5479_: *mut crate::leanh::LeanObject,
    mut v_c_5480_: *mut crate::leanh::LeanObject,
    mut v_a_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5483_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_5479_, v_c_5480_, v_a_5481_);
    return v___x_5483_;
}
pub unsafe fn l_Lean_Server_RequestM_runCoreM___boxed(
    mut v_00_u03b1_5484_: *mut crate::leanh::LeanObject,
    mut v_snap_5485_: *mut crate::leanh::LeanObject,
    mut v_c_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
    mut v_a_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5489_ =
        l_Lean_Server_RequestM_runCoreM(v_00_u03b1_5484_, v_snap_5485_, v_c_5486_, v_a_5487_);
    crate::leanh::lean_dec_ref(v_a_5487_);
    return v_res_5489_;
}
pub unsafe fn l_Lean_Server_RequestM_runTermElabM___redArg(
    mut v_snap_5490_: *mut crate::leanh::LeanObject,
    mut v_c_5491_: *mut crate::leanh::LeanObject,
    mut v_a_5492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5502_: u8 = 0;
    let mut v_a_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_a_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5517_: u8 = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_doc_5494_ = crate::leanh::lean_ctor_get(v_a_5492_, 1);
                v_toEditableDocumentCore_5495_ = crate::leanh::lean_ctor_get(v_doc_5494_, 0);
                v_meta_5496_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5495_, 0);
                crate::leanh::lean_inc_ref(v_a_5492_);
                v___x_5497_ = crate::leanh::lean_apply_1(v_c_5491_, v_a_5492_);
                v___x_5498_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(
                    v_snap_5490_,
                    v_meta_5496_,
                    v___x_5497_,
                );
                if crate::leanh::lean_obj_tag(v___x_5498_) == 0 {
                    v_a_5499_ = crate::leanh::lean_ctor_get(v___x_5498_, 0);
                    v_isSharedCheck_5511_ = (!crate::leanh::lean_is_exclusive(v___x_5498_)) as u8;
                    if v_isSharedCheck_5511_ == 0 {
                        v___x_5501_ = v___x_5498_;
                        v_isShared_5502_ = v_isSharedCheck_5511_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5499_);
                        crate::leanh::lean_dec(v___x_5498_);
                        v___x_5501_ = crate::leanh::lean_box(0);
                        v_isShared_5502_ = v_isSharedCheck_5511_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5512_ = crate::leanh::lean_ctor_get(v___x_5498_, 0);
                    crate::leanh::lean_inc(v_a_5512_);
                    crate::leanh::lean_dec_ref_known(v___x_5498_, 1);
                    v___x_5513_ = l_Lean_Server_RequestError_ofException(v_a_5512_);
                    v_a_5514_ = crate::leanh::lean_ctor_get(v___x_5513_, 0);
                    v_isSharedCheck_5521_ = (!crate::leanh::lean_is_exclusive(v___x_5513_)) as u8;
                    if v_isSharedCheck_5521_ == 0 {
                        v___x_5516_ = v___x_5513_;
                        v_isShared_5517_ = v_isSharedCheck_5521_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5514_);
                        crate::leanh::lean_dec(v___x_5513_);
                        v___x_5516_ = crate::leanh::lean_box(0);
                        v_isShared_5517_ = v_isSharedCheck_5521_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5499_) == 0 {
                    v_a_5503_ = crate::leanh::lean_ctor_get(v_a_5499_, 0);
                    crate::leanh::lean_inc(v_a_5503_);
                    crate::leanh::lean_dec_ref_known(v_a_5499_, 1);
                    if v_isShared_5502_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5501_, 1);
                        crate::leanh::lean_ctor_set(v___x_5501_, 0, v_a_5503_);
                        v___x_5505_ = v___x_5501_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5503_);
                        v___x_5505_ = v_reuseFailAlloc_5506_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5507_ = crate::leanh::lean_ctor_get(v_a_5499_, 0);
                    crate::leanh::lean_inc(v_a_5507_);
                    crate::leanh::lean_dec_ref_known(v_a_5499_, 1);
                    if v_isShared_5502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5501_, 0, v_a_5507_);
                        v___x_5509_ = v___x_5501_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5507_);
                        v___x_5509_ = v_reuseFailAlloc_5510_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5505_;
            }
            3 => {
                return v___x_5509_;
            }
            4 => {
                if v_isShared_5517_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5516_, 1);
                    v___x_5519_ = v___x_5516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
                    v___x_5519_ = v_reuseFailAlloc_5520_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_runTermElabM___redArg___boxed(
    mut v_snap_5522_: *mut crate::leanh::LeanObject,
    mut v_c_5523_: *mut crate::leanh::LeanObject,
    mut v_a_5524_: *mut crate::leanh::LeanObject,
    mut v_a_5525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5526_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_5522_, v_c_5523_, v_a_5524_);
    crate::leanh::lean_dec_ref(v_a_5524_);
    return v_res_5526_;
}
pub unsafe fn l_Lean_Server_RequestM_runTermElabM(
    mut v_00_u03b1_5527_: *mut crate::leanh::LeanObject,
    mut v_snap_5528_: *mut crate::leanh::LeanObject,
    mut v_c_5529_: *mut crate::leanh::LeanObject,
    mut v_a_5530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5532_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_5528_, v_c_5529_, v_a_5530_);
    return v___x_5532_;
}
pub unsafe fn l_Lean_Server_RequestM_runTermElabM___boxed(
    mut v_00_u03b1_5533_: *mut crate::leanh::LeanObject,
    mut v_snap_5534_: *mut crate::leanh::LeanObject,
    mut v_c_5535_: *mut crate::leanh::LeanObject,
    mut v_a_5536_: *mut crate::leanh::LeanObject,
    mut v_a_5537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5538_ =
        l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_5533_, v_snap_5534_, v_c_5535_, v_a_5536_);
    crate::leanh::lean_dec_ref(v_a_5536_);
    return v_res_5538_;
}
pub unsafe fn l_Lean_Server_SerializedLspResponse_toSerializedMessage(
    mut v_id_5545_: *mut crate::leanh::LeanObject,
    mut v_r_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serialized_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_n_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5547_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0;
                v___x_5548_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1;
                match crate::leanh::lean_obj_tag(v_id_5545_) {
                    0 => {
                        v_s_5564_ = crate::leanh::lean_ctor_get(v_id_5545_, 0);
                        v_isSharedCheck_5571_ =
                            (!crate::leanh::lean_is_exclusive(v_id_5545_)) as u8;
                        if v_isSharedCheck_5571_ == 0 {
                            v___x_5566_ = v_id_5545_;
                            v_isShared_5567_ = v_isSharedCheck_5571_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_5564_);
                            crate::leanh::lean_dec(v_id_5545_);
                            v___x_5566_ = crate::leanh::lean_box(0);
                            v_isShared_5567_ = v_isSharedCheck_5571_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        v_n_5572_ = crate::leanh::lean_ctor_get(v_id_5545_, 0);
                        v_isSharedCheck_5579_ =
                            (!crate::leanh::lean_is_exclusive(v_id_5545_)) as u8;
                        if v_isSharedCheck_5579_ == 0 {
                            v___x_5574_ = v_id_5545_;
                            v_isShared_5575_ = v_isSharedCheck_5579_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_n_5572_);
                            crate::leanh::lean_dec(v_id_5545_);
                            v___x_5574_ = crate::leanh::lean_box(0);
                            v_isShared_5575_ = v_isSharedCheck_5579_;
                            state = 4;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5580_ = crate::leanh::lean_box(0);
                        v___y_5550_ = v___x_5580_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_serialized_5551_ = crate::leanh::lean_ctor_get(v_r_5546_, 1);
                v___x_5552_ = l_Lean_Json_compress(v___y_5550_);
                v___x_5553_ = lean_string_append(v___x_5548_, v___x_5552_);
                crate::leanh::lean_dec_ref(v___x_5552_);
                v___x_5554_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2;
                v___x_5555_ = lean_string_append(v___x_5553_, v___x_5554_);
                v___x_5556_ = lean_string_append(v___x_5547_, v___x_5555_);
                crate::leanh::lean_dec_ref(v___x_5555_);
                v___x_5557_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3;
                v___x_5558_ = lean_string_append(v___x_5556_, v___x_5557_);
                v___x_5559_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4;
                v___x_5560_ = lean_string_append(v___x_5559_, v_serialized_5551_);
                v___x_5561_ = lean_string_append(v___x_5558_, v___x_5560_);
                crate::leanh::lean_dec_ref(v___x_5560_);
                v___x_5562_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5;
                v___x_5563_ = lean_string_append(v___x_5561_, v___x_5562_);
                return v___x_5563_;
            }
            2 => {
                if v_isShared_5567_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5566_, 3);
                    v___x_5569_ = v___x_5566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_s_5564_);
                    v___x_5569_ = v_reuseFailAlloc_5570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5550_ = v___x_5569_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_5575_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5574_, 2);
                    v___x_5577_ = v___x_5574_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_n_5572_);
                    v___x_5577_ = v_reuseFailAlloc_5578_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5550_ = v___x_5577_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(
    mut v_id_5581_: *mut crate::leanh::LeanObject,
    mut v_r_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_5581_, v_r_5582_);
    crate::leanh::lean_dec_ref(v_r_5582_);
    return v_res_5583_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5584_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5584_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
    v___x_5586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5586_, 0, v___x_5585_);
    return v___x_5586_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
    v___x_5589_ = lean_st_mk_ref(v___x_5588_);
    v___x_5590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5589_);
    return v___x_5590_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(
    mut v_a_5591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5592_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
    return v_res_5592_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___lam__0(
    mut v_inst_5593_: *mut crate::leanh::LeanObject,
    mut v_inst_5594_: *mut crate::leanh::LeanObject,
    mut v_j_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5604_: u8 = 0;
    let mut v_a_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5608_: u8 = 0;
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = l_Lean_Server_parseRequestParams___redArg(v_inst_5593_, v_j_5595_);
                if crate::leanh::lean_obj_tag(v___x_5596_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_5594_);
                    v_a_5597_ = crate::leanh::lean_ctor_get(v___x_5596_, 0);
                    v_isSharedCheck_5604_ = (!crate::leanh::lean_is_exclusive(v___x_5596_)) as u8;
                    if v_isSharedCheck_5604_ == 0 {
                        v___x_5599_ = v___x_5596_;
                        v_isShared_5600_ = v_isSharedCheck_5604_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5597_);
                        crate::leanh::lean_dec(v___x_5596_);
                        v___x_5599_ = crate::leanh::lean_box(0);
                        v_isShared_5600_ = v_isSharedCheck_5604_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5605_ = crate::leanh::lean_ctor_get(v___x_5596_, 0);
                    v_isSharedCheck_5613_ = (!crate::leanh::lean_is_exclusive(v___x_5596_)) as u8;
                    if v_isSharedCheck_5613_ == 0 {
                        v___x_5607_ = v___x_5596_;
                        v_isShared_5608_ = v_isSharedCheck_5613_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5605_);
                        crate::leanh::lean_dec(v___x_5596_);
                        v___x_5607_ = crate::leanh::lean_box(0);
                        v_isShared_5608_ = v_isSharedCheck_5613_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5600_ == 0 {
                    v___x_5602_ = v___x_5599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
                    v___x_5602_ = v_reuseFailAlloc_5603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5602_;
            }
            3 => {
                v___x_5609_ = crate::leanh::lean_apply_1(v_inst_5594_, v_a_5605_);
                if v_isShared_5608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5607_, 0, v___x_5609_);
                    v___x_5611_ = v___x_5607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5609_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___lam__1(
    mut v_serialize_x3f_5614_: *mut crate::leanh::LeanObject,
    mut v_a_5615_: u8,
    mut v_inst_5616_: *mut crate::leanh::LeanObject,
    mut v_r_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_serialize_x3f_5614_) == 1 {
        let mut v_val_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_5616_);
        v_val_5618_ = crate::leanh::lean_ctor_get(v_serialize_x3f_5614_, 0);
        crate::leanh::lean_inc(v_val_5618_);
        crate::leanh::lean_dec_ref_known(v_serialize_x3f_5614_, 1);
        v___x_5619_ = crate::leanh::lean_box(0);
        v___x_5620_ = crate::leanh::lean_apply_1(v_val_5618_, v_r_5617_);
        v___x_5621_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_5621_, 0, v___x_5619_);
        crate::leanh::lean_ctor_set(v___x_5621_, 1, v___x_5620_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_5621_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            v_a_5615_,
        );
        return v___x_5621_;
    } else {
        let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_serialize_x3f_5614_);
        v___x_5622_ = crate::leanh::lean_apply_1(v_inst_5616_, v_r_5617_);
        crate::leanh::lean_inc(v___x_5622_);
        v___x_5623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5623_, 0, v___x_5622_);
        v___x_5624_ = l_Lean_Json_compress(v___x_5622_);
        v___x_5625_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_5625_, 0, v___x_5623_);
        crate::leanh::lean_ctor_set(v___x_5625_, 1, v___x_5624_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_5625_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            v_a_5615_,
        );
        return v___x_5625_;
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(
    mut v_serialize_x3f_5626_: *mut crate::leanh::LeanObject,
    mut v_a_5627_: *mut crate::leanh::LeanObject,
    mut v_inst_5628_: *mut crate::leanh::LeanObject,
    mut v_r_5629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1617__boxed_5630_: u8 = 0;
    let mut v_res_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1617__boxed_5630_ = (crate::leanh::lean_unbox(v_a_5627_) as u8);
    v_res_5631_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(
        v_serialize_x3f_5626_,
        v_a_1617__boxed_5630_,
        v_inst_5628_,
        v_r_5629_,
    );
    return v_res_5631_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___lam__2(
    mut v_inst_5632_: *mut crate::leanh::LeanObject,
    mut v_handler_5633_: *mut crate::leanh::LeanObject,
    mut v___f_5634_: *mut crate::leanh::LeanObject,
    mut v_j_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_a_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut v_a_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5662_: u8 = 0;
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5638_ =
                    l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_5632_, v_j_5635_);
                if crate::leanh::lean_obj_tag(v___x_5638_) == 0 {
                    v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                    crate::leanh::lean_inc(v_a_5639_);
                    crate::leanh::lean_dec_ref_known(v___x_5638_, 1);
                    crate::leanh::lean_inc_ref(v___y_5636_);
                    v___x_5640_ = crate::leanh::lean_apply_3(
                        v_handler_5633_,
                        v_a_5639_,
                        v___y_5636_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5640_) == 0 {
                        v_a_5641_ = crate::leanh::lean_ctor_get(v___x_5640_, 0);
                        v_isSharedCheck_5650_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5640_)) as u8;
                        if v_isSharedCheck_5650_ == 0 {
                            v___x_5643_ = v___x_5640_;
                            v_isShared_5644_ = v_isSharedCheck_5650_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5641_);
                            crate::leanh::lean_dec(v___x_5640_);
                            v___x_5643_ = crate::leanh::lean_box(0);
                            v_isShared_5644_ = v_isSharedCheck_5650_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5634_);
                        v_a_5651_ = crate::leanh::lean_ctor_get(v___x_5640_, 0);
                        v_isSharedCheck_5658_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5640_)) as u8;
                        if v_isSharedCheck_5658_ == 0 {
                            v___x_5653_ = v___x_5640_;
                            v_isShared_5654_ = v_isSharedCheck_5658_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5651_);
                            crate::leanh::lean_dec(v___x_5640_);
                            v___x_5653_ = crate::leanh::lean_box(0);
                            v_isShared_5654_ = v_isSharedCheck_5658_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_5634_);
                    crate::leanh::lean_dec_ref(v_handler_5633_);
                    v_a_5659_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                    v_isSharedCheck_5666_ = (!crate::leanh::lean_is_exclusive(v___x_5638_)) as u8;
                    if v_isSharedCheck_5666_ == 0 {
                        v___x_5661_ = v___x_5638_;
                        v_isShared_5662_ = v_isSharedCheck_5666_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5659_);
                        crate::leanh::lean_dec(v___x_5638_);
                        v___x_5661_ = crate::leanh::lean_box(0);
                        v_isShared_5662_ = v_isSharedCheck_5666_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5645_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_5645_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5645_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5645_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5645_, 3, v___f_5634_);
                v___x_5646_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_5645_, v_a_5641_);
                if v_isShared_5644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5643_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
                    v___x_5648_ = v_reuseFailAlloc_5649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5648_;
            }
            3 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5656_;
            }
            5 => {
                if v_isShared_5662_ == 0 {
                    v___x_5664_ = v___x_5661_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
                    v___x_5664_ = v_reuseFailAlloc_5665_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(
    mut v_inst_5667_: *mut crate::leanh::LeanObject,
    mut v_handler_5668_: *mut crate::leanh::LeanObject,
    mut v___f_5669_: *mut crate::leanh::LeanObject,
    mut v_j_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5673_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(
        v_inst_5667_,
        v_handler_5668_,
        v___f_5669_,
        v_j_5670_,
        v___y_5671_,
    );
    crate::leanh::lean_dec_ref(v___y_5671_);
    return v_res_5673_;
}
pub unsafe fn _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5677_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_5678_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5678_, 0, v___x_5677_);
    return v___f_5678_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg(
    mut v_method_5680_: *mut crate::leanh::LeanObject,
    mut v_inst_5681_: *mut crate::leanh::LeanObject,
    mut v_inst_5682_: *mut crate::leanh::LeanObject,
    mut v_inst_5683_: *mut crate::leanh::LeanObject,
    mut v_handler_5684_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v___x_5692_: u8 = 0;
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u8 = 0;
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v_a_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5687_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_5687_) == 0 {
                    v_a_5688_ = crate::leanh::lean_ctor_get(v___x_5687_, 0);
                    v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v___x_5687_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5690_ = v___x_5687_;
                        v_isShared_5691_ = v_isSharedCheck_5724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5688_);
                        crate::leanh::lean_dec(v___x_5687_);
                        v___x_5690_ = crate::leanh::lean_box(0);
                        v_isShared_5691_ = v_isSharedCheck_5724_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_serialize_x3f_5685_);
                    crate::leanh::lean_dec_ref(v_handler_5684_);
                    crate::leanh::lean_dec_ref(v_inst_5683_);
                    crate::leanh::lean_dec_ref(v_inst_5682_);
                    crate::leanh::lean_dec_ref(v_inst_5681_);
                    crate::leanh::lean_dec_ref(v_method_5680_);
                    v_a_5725_ = crate::leanh::lean_ctor_get(v___x_5687_, 0);
                    v_isSharedCheck_5732_ = (!crate::leanh::lean_is_exclusive(v___x_5687_)) as u8;
                    if v_isSharedCheck_5732_ == 0 {
                        v___x_5727_ = v___x_5687_;
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5725_);
                        crate::leanh::lean_dec(v___x_5687_);
                        v___x_5727_ = crate::leanh::lean_box(0);
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5692_ = (crate::leanh::lean_unbox(v_a_5688_) as u8);
                if v___x_5692_ == 0 {
                    crate::leanh::lean_dec(v_a_5688_);
                    crate::leanh::lean_dec(v_serialize_x3f_5685_);
                    crate::leanh::lean_dec_ref(v_handler_5684_);
                    crate::leanh::lean_dec_ref(v_inst_5683_);
                    crate::leanh::lean_dec_ref(v_inst_5682_);
                    crate::leanh::lean_dec_ref(v_inst_5681_);
                    v___x_5693_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__0;
                    v___x_5694_ = lean_string_append(v___x_5693_, v_method_5680_);
                    crate::leanh::lean_dec_ref(v_method_5680_);
                    v___x_5695_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__1;
                    v___x_5696_ = lean_string_append(v___x_5694_, v___x_5695_);
                    v___x_5697_ = lean_mk_io_user_error(v___x_5696_);
                    if v_isShared_5691_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5690_, 1);
                        crate::leanh::lean_ctor_set(v___x_5690_, 0, v___x_5697_);
                        v___x_5699_ = v___x_5690_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5697_);
                        v___x_5699_ = v_reuseFailAlloc_5700_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5701_ = l_Lean_Server_requestHandlers;
                    v___x_5702_ = lean_st_ref_get(v___x_5701_);
                    v___x_5703_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__2;
                    v___f_5704_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerLspRequestHandler___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once
                        ),
                        _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3,
                    );
                    crate::leanh::lean_inc_ref(v_method_5680_);
                    v___x_5705_ = l_Lean_PersistentHashMap_contains___redArg(
                        v___f_5704_,
                        v___x_5703_,
                        v___x_5702_,
                        v_method_5680_,
                    );
                    if v___x_5705_ == 0 {
                        v___x_5706_ = lean_st_ref_take(v___x_5701_);
                        crate::leanh::lean_inc_ref(v_inst_5681_);
                        v___f_5707_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Server_registerLspRequestHandler___redArg___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_5707_, 0, v_inst_5681_);
                        crate::leanh::lean_closure_set(v___f_5707_, 1, v_inst_5682_);
                        v___f_5708_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_5708_, 0, v_serialize_x3f_5685_);
                        crate::leanh::lean_closure_set(v___f_5708_, 1, v_a_5688_);
                        crate::leanh::lean_closure_set(v___f_5708_, 2, v_inst_5683_);
                        v___f_5709_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            6,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_5709_, 0, v_inst_5681_);
                        crate::leanh::lean_closure_set(v___f_5709_, 1, v_handler_5684_);
                        crate::leanh::lean_closure_set(v___f_5709_, 2, v___f_5708_);
                        v___x_5710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5710_, 0, v___f_5707_);
                        crate::leanh::lean_ctor_set(v___x_5710_, 1, v___f_5709_);
                        v___x_5711_ = l_Lean_PersistentHashMap_insert___redArg(
                            v___f_5704_,
                            v___x_5703_,
                            v___x_5706_,
                            v_method_5680_,
                            v___x_5710_,
                        );
                        v___x_5712_ = lean_st_ref_set(v___x_5701_, v___x_5711_);
                        if v_isShared_5691_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5690_, 0, v___x_5712_);
                            v___x_5714_ = v___x_5690_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5715_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
                            v___x_5714_ = v_reuseFailAlloc_5715_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5688_);
                        crate::leanh::lean_dec(v_serialize_x3f_5685_);
                        crate::leanh::lean_dec_ref(v_handler_5684_);
                        crate::leanh::lean_dec_ref(v_inst_5683_);
                        crate::leanh::lean_dec_ref(v_inst_5682_);
                        crate::leanh::lean_dec_ref(v_inst_5681_);
                        v___x_5716_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__0;
                        v___x_5717_ = lean_string_append(v___x_5716_, v_method_5680_);
                        crate::leanh::lean_dec_ref(v_method_5680_);
                        v___x_5718_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__4;
                        v___x_5719_ = lean_string_append(v___x_5717_, v___x_5718_);
                        v___x_5720_ = lean_mk_io_user_error(v___x_5719_);
                        if v_isShared_5691_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5690_, 1);
                            crate::leanh::lean_ctor_set(v___x_5690_, 0, v___x_5720_);
                            v___x_5722_ = v___x_5690_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5723_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v___x_5720_);
                            v___x_5722_ = v_reuseFailAlloc_5723_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5699_;
            }
            3 => {
                return v___x_5714_;
            }
            4 => {
                return v___x_5722_;
            }
            5 => {
                if v_isShared_5728_ == 0 {
                    v___x_5730_ = v___x_5727_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_a_5725_);
                    v___x_5730_ = v_reuseFailAlloc_5731_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___redArg___boxed(
    mut v_method_5733_: *mut crate::leanh::LeanObject,
    mut v_inst_5734_: *mut crate::leanh::LeanObject,
    mut v_inst_5735_: *mut crate::leanh::LeanObject,
    mut v_inst_5736_: *mut crate::leanh::LeanObject,
    mut v_handler_5737_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5738_: *mut crate::leanh::LeanObject,
    mut v_a_5739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5740_ = l_Lean_Server_registerLspRequestHandler___redArg(
        v_method_5733_,
        v_inst_5734_,
        v_inst_5735_,
        v_inst_5736_,
        v_handler_5737_,
        v_serialize_x3f_5738_,
    );
    return v_res_5740_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler(
    mut v_method_5741_: *mut crate::leanh::LeanObject,
    mut v_paramType_5742_: *mut crate::leanh::LeanObject,
    mut v_inst_5743_: *mut crate::leanh::LeanObject,
    mut v_inst_5744_: *mut crate::leanh::LeanObject,
    mut v_respType_5745_: *mut crate::leanh::LeanObject,
    mut v_inst_5746_: *mut crate::leanh::LeanObject,
    mut v_handler_5747_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_Server_registerLspRequestHandler___redArg(
        v_method_5741_,
        v_inst_5743_,
        v_inst_5744_,
        v_inst_5746_,
        v_handler_5747_,
        v_serialize_x3f_5748_,
    );
    return v___x_5750_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___boxed(
    mut v_method_5751_: *mut crate::leanh::LeanObject,
    mut v_paramType_5752_: *mut crate::leanh::LeanObject,
    mut v_inst_5753_: *mut crate::leanh::LeanObject,
    mut v_inst_5754_: *mut crate::leanh::LeanObject,
    mut v_respType_5755_: *mut crate::leanh::LeanObject,
    mut v_inst_5756_: *mut crate::leanh::LeanObject,
    mut v_handler_5757_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5758_: *mut crate::leanh::LeanObject,
    mut v_a_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_Lean_Server_registerLspRequestHandler(
        v_method_5751_,
        v_paramType_5752_,
        v_inst_5753_,
        v_inst_5754_,
        v_respType_5755_,
        v_inst_5756_,
        v_handler_5757_,
        v_serialize_x3f_5758_,
    );
    return v_res_5760_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(
    mut v_keys_5761_: *mut crate::leanh::LeanObject,
    mut v_vals_5762_: *mut crate::leanh::LeanObject,
    mut v_i_5763_: *mut crate::leanh::LeanObject,
    mut v_k_5764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: u8 = 0;
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: u8 = 0;
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5765_ = lean_array_get_size(v_keys_5761_);
                v___x_5766_ = lean_nat_dec_lt(v_i_5763_, v___x_5765_);
                if v___x_5766_ == 0 {
                    crate::leanh::lean_dec(v_i_5763_);
                    v___x_5767_ = crate::leanh::lean_box(0);
                    return v___x_5767_;
                } else {
                    v_k_x27_5768_ = lean_array_fget_borrowed(v_keys_5761_, v_i_5763_);
                    v___x_5769_ = lean_string_dec_eq(v_k_5764_, v_k_x27_5768_);
                    if v___x_5769_ == 0 {
                        v___x_5770_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5771_ = lean_nat_add(v_i_5763_, v___x_5770_);
                        crate::leanh::lean_dec(v_i_5763_);
                        v_i_5763_ = v___x_5771_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5773_ = lean_array_fget_borrowed(v_vals_5762_, v_i_5763_);
                        crate::leanh::lean_dec(v_i_5763_);
                        crate::leanh::lean_inc(v___x_5773_);
                        v___x_5774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5774_, 0, v___x_5773_);
                        return v___x_5774_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_5775_: *mut crate::leanh::LeanObject,
    mut v_vals_5776_: *mut crate::leanh::LeanObject,
    mut v_i_5777_: *mut crate::leanh::LeanObject,
    mut v_k_5778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5779_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_5775_, v_vals_5776_, v_i_5777_, v_k_5778_);
    crate::leanh::lean_dec_ref(v_k_5778_);
    crate::leanh::lean_dec_ref(v_vals_5776_);
    crate::leanh::lean_dec_ref(v_keys_5775_);
    return v_res_5779_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_5780_: usize = 0;
    let mut v___x_5781_: usize = 0;
    let mut v___x_5782_: usize = 0;
    v___x_5780_ = 5usize;
    v___x_5781_ = 1usize;
    v___x_5782_ = lean_usize_shift_left(v___x_5781_, v___x_5780_);
    return v___x_5782_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5785_: usize = 0;
    v___x_5783_ = 1usize;
    v___x_5784_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0);
    v___x_5785_ = lean_usize_sub(v___x_5784_, v___x_5783_);
    return v___x_5785_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(
    mut v_x_5786_: *mut crate::leanh::LeanObject,
    mut v_x_5787_: usize,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: usize = 0;
    let mut v___x_5792_: usize = 0;
    let mut v___x_5793_: usize = 0;
    let mut v_j_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: u8 = 0;
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: usize = 0;
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5786_) == 0 {
                    v_es_5789_ = crate::leanh::lean_ctor_get(v_x_5786_, 0);
                    v___x_5790_ = crate::leanh::lean_box(2);
                    v___x_5791_ = 5usize;
                    v___x_5792_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1);
                    v___x_5793_ = lean_usize_land(v_x_5787_, v___x_5792_);
                    v_j_5794_ = lean_usize_to_nat(v___x_5793_);
                    v___x_5795_ = lean_array_get_borrowed(v___x_5790_, v_es_5789_, v_j_5794_);
                    crate::leanh::lean_dec(v_j_5794_);
                    match crate::leanh::lean_obj_tag(v___x_5795_) {
                        0 => {
                            v_key_5796_ = crate::leanh::lean_ctor_get(v___x_5795_, 0);
                            v_val_5797_ = crate::leanh::lean_ctor_get(v___x_5795_, 1);
                            v___x_5798_ = lean_string_dec_eq(v_x_5788_, v_key_5796_);
                            if v___x_5798_ == 0 {
                                v___x_5799_ = crate::leanh::lean_box(0);
                                return v___x_5799_;
                            } else {
                                crate::leanh::lean_inc(v_val_5797_);
                                v___x_5800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5800_, 0, v_val_5797_);
                                return v___x_5800_;
                            }
                        }
                        1 => {
                            v_node_5801_ = crate::leanh::lean_ctor_get(v___x_5795_, 0);
                            v___x_5802_ = lean_usize_shift_right(v_x_5787_, v___x_5791_);
                            v_x_5786_ = v_node_5801_;
                            v_x_5787_ = v___x_5802_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5804_ = crate::leanh::lean_box(0);
                            return v___x_5804_;
                        }
                    }
                } else {
                    v_ks_5805_ = crate::leanh::lean_ctor_get(v_x_5786_, 0);
                    v_vs_5806_ = crate::leanh::lean_ctor_get(v_x_5786_, 1);
                    v___x_5807_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5808_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_5805_, v_vs_5806_, v___x_5807_, v_x_5788_);
                    return v___x_5808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(
    mut v_x_5809_: *mut crate::leanh::LeanObject,
    mut v_x_5810_: *mut crate::leanh::LeanObject,
    mut v_x_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_279__boxed_5812_: usize = 0;
    let mut v_res_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_279__boxed_5812_ = crate::leanh::lean_unbox_usize(v_x_5810_);
    crate::leanh::lean_dec(v_x_5810_);
    v_res_5813_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_5809_, v_x_279__boxed_5812_, v_x_5811_);
    crate::leanh::lean_dec_ref(v_x_5811_);
    crate::leanh::lean_dec_ref(v_x_5809_);
    return v_res_5813_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(
    mut v_x_5814_: *mut crate::leanh::LeanObject,
    mut v_x_5815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5816_: u64 = 0;
    let mut v___x_5817_: usize = 0;
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5816_ = lean_string_hash(v_x_5815_);
    v___x_5817_ = lean_uint64_to_usize(v___x_5816_);
    v___x_5818_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_5814_, v___x_5817_, v_x_5815_);
    return v___x_5818_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(
    mut v_x_5819_: *mut crate::leanh::LeanObject,
    mut v_x_5820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_5819_, v_x_5820_);
    crate::leanh::lean_dec_ref(v_x_5820_);
    crate::leanh::lean_dec_ref(v_x_5819_);
    return v_res_5821_;
}
pub unsafe fn l_Lean_Server_lookupLspRequestHandler(
    mut v_method_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_Server_requestHandlers;
    v___x_5825_ = lean_st_ref_get(v___x_5824_);
    v___x_5826_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_5825_, v_method_5822_);
    crate::leanh::lean_dec(v___x_5825_);
    v___x_5827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5827_, 0, v___x_5826_);
    return v___x_5827_;
}
pub unsafe fn l_Lean_Server_lookupLspRequestHandler___boxed(
    mut v_method_5828_: *mut crate::leanh::LeanObject,
    mut v_a_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Lean_Server_lookupLspRequestHandler(v_method_5828_);
    crate::leanh::lean_dec_ref(v_method_5828_);
    return v_res_5830_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(
    mut v_00_u03b2_5831_: *mut crate::leanh::LeanObject,
    mut v_x_5832_: *mut crate::leanh::LeanObject,
    mut v_x_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5834_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_5832_, v_x_5833_);
    return v___x_5834_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(
    mut v_00_u03b2_5835_: *mut crate::leanh::LeanObject,
    mut v_x_5836_: *mut crate::leanh::LeanObject,
    mut v_x_5837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5838_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(
            v_00_u03b2_5835_,
            v_x_5836_,
            v_x_5837_,
        );
    crate::leanh::lean_dec_ref(v_x_5837_);
    crate::leanh::lean_dec_ref(v_x_5836_);
    return v_res_5838_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(
    mut v_00_u03b2_5839_: *mut crate::leanh::LeanObject,
    mut v_x_5840_: *mut crate::leanh::LeanObject,
    mut v_x_5841_: usize,
    mut v_x_5842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_5840_, v_x_5841_, v_x_5842_);
    return v___x_5843_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(
    mut v_00_u03b2_5844_: *mut crate::leanh::LeanObject,
    mut v_x_5845_: *mut crate::leanh::LeanObject,
    mut v_x_5846_: *mut crate::leanh::LeanObject,
    mut v_x_5847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_363__boxed_5848_: usize = 0;
    let mut v_res_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_363__boxed_5848_ = crate::leanh::lean_unbox_usize(v_x_5846_);
    crate::leanh::lean_dec(v_x_5846_);
    v_res_5849_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_5844_, v_x_5845_, v_x_363__boxed_5848_, v_x_5847_);
    crate::leanh::lean_dec_ref(v_x_5847_);
    crate::leanh::lean_dec_ref(v_x_5845_);
    return v_res_5849_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5850_: *mut crate::leanh::LeanObject,
    mut v_keys_5851_: *mut crate::leanh::LeanObject,
    mut v_vals_5852_: *mut crate::leanh::LeanObject,
    mut v_heq_5853_: *mut crate::leanh::LeanObject,
    mut v_i_5854_: *mut crate::leanh::LeanObject,
    mut v_k_5855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5856_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_5851_, v_vals_5852_, v_i_5854_, v_k_5855_);
    return v___x_5856_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5857_: *mut crate::leanh::LeanObject,
    mut v_keys_5858_: *mut crate::leanh::LeanObject,
    mut v_vals_5859_: *mut crate::leanh::LeanObject,
    mut v_heq_5860_: *mut crate::leanh::LeanObject,
    mut v_i_5861_: *mut crate::leanh::LeanObject,
    mut v_k_5862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5863_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_5857_, v_keys_5858_, v_vals_5859_, v_heq_5860_, v_i_5861_, v_k_5862_);
    crate::leanh::lean_dec_ref(v_k_5862_);
    crate::leanh::lean_dec_ref(v_vals_5859_);
    crate::leanh::lean_dec_ref(v_keys_5858_);
    return v_res_5863_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__0(
    mut v_inst_5867_: *mut crate::leanh::LeanObject,
    mut v_method_5868_: *mut crate::leanh::LeanObject,
    mut v_x_5869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_response_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v_a_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5890_: u8 = 0;
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut v_a_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_a_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_x3f_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serialized_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut v_a_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5869_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_5867_);
                    v_a_5895_ = crate::leanh::lean_ctor_get(v_x_5869_, 0);
                    v_isSharedCheck_5902_ = (!crate::leanh::lean_is_exclusive(v_x_5869_)) as u8;
                    if v_isSharedCheck_5902_ == 0 {
                        v___x_5897_ = v_x_5869_;
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5895_);
                        crate::leanh::lean_dec(v_x_5869_);
                        v___x_5897_ = crate::leanh::lean_box(0);
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_5903_ = crate::leanh::lean_ctor_get(v_x_5869_, 0);
                    crate::leanh::lean_inc(v_a_5903_);
                    crate::leanh::lean_dec_ref_known(v_x_5869_, 1);
                    v_response_x3f_5904_ = crate::leanh::lean_ctor_get(v_a_5903_, 0);
                    if crate::leanh::lean_obj_tag(v_response_x3f_5904_) == 0 {
                        v_serialized_5905_ = crate::leanh::lean_ctor_get(v_a_5903_, 1);
                        crate::leanh::lean_inc_ref(v_serialized_5905_);
                        crate::leanh::lean_dec(v_a_5903_);
                        v___x_5906_ = l_Lean_Json_parse(v_serialized_5905_);
                        if crate::leanh::lean_obj_tag(v___x_5906_) == 0 {
                            crate::leanh::lean_dec_ref(v_inst_5867_);
                            v_a_5907_ = crate::leanh::lean_ctor_get(v___x_5906_, 0);
                            v_isSharedCheck_5920_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5906_)) as u8;
                            if v_isSharedCheck_5920_ == 0 {
                                v___x_5909_ = v___x_5906_;
                                v_isShared_5910_ = v_isSharedCheck_5920_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5907_);
                                crate::leanh::lean_dec(v___x_5906_);
                                v___x_5909_ = crate::leanh::lean_box(0);
                                v_isShared_5910_ = v_isSharedCheck_5920_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_5921_ = crate::leanh::lean_ctor_get(v___x_5906_, 0);
                            crate::leanh::lean_inc(v_a_5921_);
                            crate::leanh::lean_dec_ref_known(v___x_5906_, 1);
                            v_response_5871_ = v_a_5921_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_response_x3f_5904_);
                        crate::leanh::lean_dec(v_a_5903_);
                        v_val_5922_ = crate::leanh::lean_ctor_get(v_response_x3f_5904_, 0);
                        crate::leanh::lean_inc(v_val_5922_);
                        crate::leanh::lean_dec_ref_known(v_response_x3f_5904_, 1);
                        v_response_5871_ = v_val_5922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5872_ = crate::leanh::lean_apply_1(v_inst_5867_, v_response_5871_);
                if crate::leanh::lean_obj_tag(v___x_5872_) == 0 {
                    v_a_5873_ = crate::leanh::lean_ctor_get(v___x_5872_, 0);
                    v_isSharedCheck_5886_ = (!crate::leanh::lean_is_exclusive(v___x_5872_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v___x_5875_ = v___x_5872_;
                        v_isShared_5876_ = v_isSharedCheck_5886_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5873_);
                        crate::leanh::lean_dec(v___x_5872_);
                        v___x_5875_ = crate::leanh::lean_box(0);
                        v_isShared_5876_ = v_isSharedCheck_5886_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5887_ = crate::leanh::lean_ctor_get(v___x_5872_, 0);
                    v_isSharedCheck_5894_ = (!crate::leanh::lean_is_exclusive(v___x_5872_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v___x_5889_ = v___x_5872_;
                        v_isShared_5890_ = v_isSharedCheck_5894_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5887_);
                        crate::leanh::lean_dec(v___x_5872_);
                        v___x_5889_ = crate::leanh::lean_box(0);
                        v_isShared_5890_ = v_isSharedCheck_5894_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5877_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0;
                v___x_5878_ = lean_string_append(v___x_5877_, v_method_5868_);
                v___x_5879_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1;
                v___x_5880_ = lean_string_append(v___x_5878_, v___x_5879_);
                v___x_5881_ = lean_string_append(v___x_5880_, v_a_5873_);
                crate::leanh::lean_dec(v_a_5873_);
                v___x_5882_ = l_Lean_Server_RequestError_internalError(v___x_5881_);
                if v_isShared_5876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5882_);
                    v___x_5884_ = v___x_5875_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5882_);
                    v___x_5884_ = v_reuseFailAlloc_5885_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5884_;
            }
            4 => {
                if v_isShared_5890_ == 0 {
                    v___x_5892_ = v___x_5889_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
                    v___x_5892_ = v_reuseFailAlloc_5893_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5892_;
            }
            6 => {
                if v_isShared_5898_ == 0 {
                    v___x_5900_ = v___x_5897_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
                    v___x_5900_ = v_reuseFailAlloc_5901_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5900_;
            }
            8 => {
                v___x_5911_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2;
                v___x_5912_ = lean_string_append(v___x_5911_, v_method_5868_);
                v___x_5913_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1;
                v___x_5914_ = lean_string_append(v___x_5912_, v___x_5913_);
                v___x_5915_ = lean_string_append(v___x_5914_, v_a_5907_);
                crate::leanh::lean_dec(v_a_5907_);
                v___x_5916_ = l_Lean_Server_RequestError_internalError(v___x_5915_);
                if v_isShared_5910_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5909_, 0, v___x_5916_);
                    v___x_5918_ = v___x_5909_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5919_, 0, v___x_5916_);
                    v___x_5918_ = v_reuseFailAlloc_5919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(
    mut v_inst_5923_: *mut crate::leanh::LeanObject,
    mut v_method_5924_: *mut crate::leanh::LeanObject,
    mut v_x_5925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5926_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(
        v_inst_5923_,
        v_method_5924_,
        v_x_5925_,
    );
    crate::leanh::lean_dec_ref(v_method_5924_);
    return v_res_5926_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__1(
    mut v_inst_5927_: *mut crate::leanh::LeanObject,
    mut v_a_5928_: u8,
    mut v_r_5929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5930_ = crate::leanh::lean_apply_1(v_inst_5927_, v_r_5929_);
    crate::leanh::lean_inc(v___x_5930_);
    v___x_5931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5931_, 0, v___x_5930_);
    v___x_5932_ = l_Lean_Json_compress(v___x_5930_);
    v___x_5933_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5933_, 0, v___x_5931_);
    crate::leanh::lean_ctor_set(v___x_5933_, 1, v___x_5932_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5933_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_a_5928_,
    );
    return v___x_5933_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(
    mut v_inst_5934_: *mut crate::leanh::LeanObject,
    mut v_a_5935_: *mut crate::leanh::LeanObject,
    mut v_r_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2455__boxed_5937_: u8 = 0;
    let mut v_res_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_2455__boxed_5937_ = (crate::leanh::lean_unbox(v_a_5935_) as u8);
    v_res_5938_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(
        v_inst_5934_,
        v_a_2455__boxed_5937_,
        v_r_5936_,
    );
    return v_res_5938_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__2(
    mut v_handle_5939_: *mut crate::leanh::LeanObject,
    mut v_inst_5940_: *mut crate::leanh::LeanObject,
    mut v___f_5941_: *mut crate::leanh::LeanObject,
    mut v_handler_5942_: *mut crate::leanh::LeanObject,
    mut v___f_5943_: *mut crate::leanh::LeanObject,
    mut v_j_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5956_: u8 = 0;
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v_a_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut v_a_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5974_: u8 = 0;
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_5945_);
                crate::leanh::lean_inc(v_j_5944_);
                v___x_5947_ = crate::leanh::lean_apply_3(
                    v_handle_5939_,
                    v_j_5944_,
                    v___y_5945_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5947_) == 0 {
                    v_a_5948_ = crate::leanh::lean_ctor_get(v___x_5947_, 0);
                    crate::leanh::lean_inc(v_a_5948_);
                    crate::leanh::lean_dec_ref_known(v___x_5947_, 1);
                    v___x_5949_ =
                        l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_5940_, v_j_5944_);
                    if crate::leanh::lean_obj_tag(v___x_5949_) == 0 {
                        v_a_5950_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                        crate::leanh::lean_inc(v_a_5950_);
                        crate::leanh::lean_dec_ref_known(v___x_5949_, 1);
                        v___x_5951_ =
                            l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5941_, v_a_5948_);
                        crate::leanh::lean_inc_ref(v___y_5945_);
                        v___x_5952_ = crate::leanh::lean_apply_4(
                            v_handler_5942_,
                            v_a_5950_,
                            v___x_5951_,
                            v___y_5945_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5952_) == 0 {
                            v_a_5953_ = crate::leanh::lean_ctor_get(v___x_5952_, 0);
                            v_isSharedCheck_5962_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5952_)) as u8;
                            if v_isSharedCheck_5962_ == 0 {
                                v___x_5955_ = v___x_5952_;
                                v_isShared_5956_ = v_isSharedCheck_5962_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5953_);
                                crate::leanh::lean_dec(v___x_5952_);
                                v___x_5955_ = crate::leanh::lean_box(0);
                                v_isShared_5956_ = v_isSharedCheck_5962_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_5943_);
                            v_a_5963_ = crate::leanh::lean_ctor_get(v___x_5952_, 0);
                            v_isSharedCheck_5970_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5952_)) as u8;
                            if v_isSharedCheck_5970_ == 0 {
                                v___x_5965_ = v___x_5952_;
                                v_isShared_5966_ = v_isSharedCheck_5970_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5963_);
                                crate::leanh::lean_dec(v___x_5952_);
                                v___x_5965_ = crate::leanh::lean_box(0);
                                v_isShared_5966_ = v_isSharedCheck_5970_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5948_);
                        crate::leanh::lean_dec_ref(v___f_5943_);
                        crate::leanh::lean_dec_ref(v_handler_5942_);
                        crate::leanh::lean_dec_ref(v___f_5941_);
                        v_a_5971_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                        v_isSharedCheck_5978_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5949_)) as u8;
                        if v_isSharedCheck_5978_ == 0 {
                            v___x_5973_ = v___x_5949_;
                            v_isShared_5974_ = v_isSharedCheck_5978_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5971_);
                            crate::leanh::lean_dec(v___x_5949_);
                            v___x_5973_ = crate::leanh::lean_box(0);
                            v_isShared_5974_ = v_isSharedCheck_5978_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_j_5944_);
                    crate::leanh::lean_dec_ref(v___f_5943_);
                    crate::leanh::lean_dec_ref(v_handler_5942_);
                    crate::leanh::lean_dec_ref(v___f_5941_);
                    crate::leanh::lean_dec_ref(v_inst_5940_);
                    return v___x_5947_;
                }
            }
            1 => {
                v___x_5957_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_5957_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5957_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5957_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5957_, 3, v___f_5943_);
                v___x_5958_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_5957_, v_a_5953_);
                if v_isShared_5956_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5955_, 0, v___x_5958_);
                    v___x_5960_ = v___x_5955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5958_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5960_;
            }
            3 => {
                if v_isShared_5966_ == 0 {
                    v___x_5968_ = v___x_5965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
                    v___x_5968_ = v_reuseFailAlloc_5969_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5968_;
            }
            5 => {
                if v_isShared_5974_ == 0 {
                    v___x_5976_ = v___x_5973_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5971_);
                    v___x_5976_ = v_reuseFailAlloc_5977_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(
    mut v_handle_5979_: *mut crate::leanh::LeanObject,
    mut v_inst_5980_: *mut crate::leanh::LeanObject,
    mut v___f_5981_: *mut crate::leanh::LeanObject,
    mut v_handler_5982_: *mut crate::leanh::LeanObject,
    mut v___f_5983_: *mut crate::leanh::LeanObject,
    mut v_j_5984_: *mut crate::leanh::LeanObject,
    mut v___y_5985_: *mut crate::leanh::LeanObject,
    mut v___y_5986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5987_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(
        v_handle_5979_,
        v_inst_5980_,
        v___f_5981_,
        v_handler_5982_,
        v___f_5983_,
        v_j_5984_,
        v___y_5985_,
    );
    crate::leanh::lean_dec_ref(v___y_5985_);
    return v_res_5987_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg(
    mut v_method_5990_: *mut crate::leanh::LeanObject,
    mut v_inst_5991_: *mut crate::leanh::LeanObject,
    mut v_inst_5992_: *mut crate::leanh::LeanObject,
    mut v_inst_5993_: *mut crate::leanh::LeanObject,
    mut v_handler_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6000_: u8 = 0;
    let mut v___x_6001_: u8 = 0;
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v_val_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileSource_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_handle_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v___f_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6045_: u8 = 0;
    let mut v_isSharedCheck_6046_: u8 = 0;
    let mut v_a_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6050_: u8 = 0;
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5996_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_5996_) == 0 {
                    v_a_5997_ = crate::leanh::lean_ctor_get(v___x_5996_, 0);
                    v_isSharedCheck_6046_ = (!crate::leanh::lean_is_exclusive(v___x_5996_)) as u8;
                    if v_isSharedCheck_6046_ == 0 {
                        v___x_5999_ = v___x_5996_;
                        v_isShared_6000_ = v_isSharedCheck_6046_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5997_);
                        crate::leanh::lean_dec(v___x_5996_);
                        v___x_5999_ = crate::leanh::lean_box(0);
                        v_isShared_6000_ = v_isSharedCheck_6046_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_handler_5994_);
                    crate::leanh::lean_dec_ref(v_inst_5993_);
                    crate::leanh::lean_dec_ref(v_inst_5992_);
                    crate::leanh::lean_dec_ref(v_inst_5991_);
                    crate::leanh::lean_dec_ref(v_method_5990_);
                    v_a_6047_ = crate::leanh::lean_ctor_get(v___x_5996_, 0);
                    v_isSharedCheck_6054_ = (!crate::leanh::lean_is_exclusive(v___x_5996_)) as u8;
                    if v_isSharedCheck_6054_ == 0 {
                        v___x_6049_ = v___x_5996_;
                        v_isShared_6050_ = v_isSharedCheck_6054_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6047_);
                        crate::leanh::lean_dec(v___x_5996_);
                        v___x_6049_ = crate::leanh::lean_box(0);
                        v_isShared_6050_ = v_isSharedCheck_6054_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6001_ = (crate::leanh::lean_unbox(v_a_5997_) as u8);
                if v___x_6001_ == 0 {
                    crate::leanh::lean_dec(v_a_5997_);
                    crate::leanh::lean_dec_ref(v_handler_5994_);
                    crate::leanh::lean_dec_ref(v_inst_5993_);
                    crate::leanh::lean_dec_ref(v_inst_5992_);
                    crate::leanh::lean_dec_ref(v_inst_5991_);
                    v___x_6002_ = l_Lean_Server_chainLspRequestHandler___redArg___closed__0;
                    v___x_6003_ = lean_string_append(v___x_6002_, v_method_5990_);
                    crate::leanh::lean_dec_ref(v_method_5990_);
                    v___x_6004_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__1;
                    v___x_6005_ = lean_string_append(v___x_6003_, v___x_6004_);
                    v___x_6006_ = lean_mk_io_user_error(v___x_6005_);
                    if v_isShared_6000_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5999_, 1);
                        crate::leanh::lean_ctor_set(v___x_5999_, 0, v___x_6006_);
                        v___x_6008_ = v___x_5999_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6009_, 0, v___x_6006_);
                        v___x_6008_ = v_reuseFailAlloc_6009_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5999_);
                    v___x_6010_ = l_Lean_Server_lookupLspRequestHandler(v_method_5990_);
                    v_a_6011_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                    v_isSharedCheck_6045_ = (!crate::leanh::lean_is_exclusive(v___x_6010_)) as u8;
                    if v_isSharedCheck_6045_ == 0 {
                        v___x_6013_ = v___x_6010_;
                        v_isShared_6014_ = v_isSharedCheck_6045_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6011_);
                        crate::leanh::lean_dec(v___x_6010_);
                        v___x_6013_ = crate::leanh::lean_box(0);
                        v_isShared_6014_ = v_isSharedCheck_6045_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6008_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_6011_) == 1 {
                    v_val_6015_ = crate::leanh::lean_ctor_get(v_a_6011_, 0);
                    crate::leanh::lean_inc(v_val_6015_);
                    crate::leanh::lean_dec_ref_known(v_a_6011_, 1);
                    v___x_6016_ = l_Lean_Server_requestHandlers;
                    v___x_6017_ = lean_st_ref_take(v___x_6016_);
                    v_fileSource_6018_ = crate::leanh::lean_ctor_get(v_val_6015_, 0);
                    v_handle_6019_ = crate::leanh::lean_ctor_get(v_val_6015_, 1);
                    v_isSharedCheck_6036_ = (!crate::leanh::lean_is_exclusive(v_val_6015_)) as u8;
                    if v_isSharedCheck_6036_ == 0 {
                        v___x_6021_ = v_val_6015_;
                        v_isShared_6022_ = v_isSharedCheck_6036_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_handle_6019_);
                        crate::leanh::lean_inc(v_fileSource_6018_);
                        crate::leanh::lean_dec(v_val_6015_);
                        v___x_6021_ = crate::leanh::lean_box(0);
                        v_isShared_6022_ = v_isSharedCheck_6036_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6011_);
                    crate::leanh::lean_dec(v_a_5997_);
                    crate::leanh::lean_dec_ref(v_handler_5994_);
                    crate::leanh::lean_dec_ref(v_inst_5993_);
                    crate::leanh::lean_dec_ref(v_inst_5992_);
                    crate::leanh::lean_dec_ref(v_inst_5991_);
                    v___x_6037_ = l_Lean_Server_chainLspRequestHandler___redArg___closed__0;
                    v___x_6038_ = lean_string_append(v___x_6037_, v_method_5990_);
                    crate::leanh::lean_dec_ref(v_method_5990_);
                    v___x_6039_ = l_Lean_Server_chainLspRequestHandler___redArg___closed__1;
                    v___x_6040_ = lean_string_append(v___x_6038_, v___x_6039_);
                    v___x_6041_ = lean_mk_io_user_error(v___x_6040_);
                    if v_isShared_6014_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6013_, 1);
                        crate::leanh::lean_ctor_set(v___x_6013_, 0, v___x_6041_);
                        v___x_6043_ = v___x_6013_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6044_, 0, v___x_6041_);
                        v___x_6043_ = v_reuseFailAlloc_6044_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_method_5990_);
                v___f_6023_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6023_, 0, v_inst_5992_);
                crate::leanh::lean_closure_set(v___f_6023_, 1, v_method_5990_);
                v___x_6024_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__2;
                v___f_6025_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6025_, 0, v_inst_5993_);
                crate::leanh::lean_closure_set(v___f_6025_, 1, v_a_5997_);
                v___f_6026_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    8,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_6026_, 0, v_handle_6019_);
                crate::leanh::lean_closure_set(v___f_6026_, 1, v_inst_5991_);
                crate::leanh::lean_closure_set(v___f_6026_, 2, v___f_6023_);
                crate::leanh::lean_closure_set(v___f_6026_, 3, v_handler_5994_);
                crate::leanh::lean_closure_set(v___f_6026_, 4, v___f_6025_);
                v___f_6027_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_registerLspRequestHandler___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once
                    ),
                    _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3,
                );
                if v_isShared_6022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6021_, 1, v___f_6026_);
                    v___x_6029_ = v___x_6021_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6035_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_fileSource_6018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 1, v___f_6026_);
                    v___x_6029_ = v_reuseFailAlloc_6035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6030_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_6027_,
                    v___x_6024_,
                    v___x_6017_,
                    v_method_5990_,
                    v___x_6029_,
                );
                v___x_6031_ = lean_st_ref_set(v___x_6016_, v___x_6030_);
                if v_isShared_6014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6013_, 0, v___x_6031_);
                    v___x_6033_ = v___x_6013_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6034_, 0, v___x_6031_);
                    v___x_6033_ = v_reuseFailAlloc_6034_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6033_;
            }
            7 => {
                return v___x_6043_;
            }
            8 => {
                if v_isShared_6050_ == 0 {
                    v___x_6052_ = v___x_6049_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
                    v___x_6052_ = v_reuseFailAlloc_6053_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___redArg___boxed(
    mut v_method_6055_: *mut crate::leanh::LeanObject,
    mut v_inst_6056_: *mut crate::leanh::LeanObject,
    mut v_inst_6057_: *mut crate::leanh::LeanObject,
    mut v_inst_6058_: *mut crate::leanh::LeanObject,
    mut v_handler_6059_: *mut crate::leanh::LeanObject,
    mut v_a_6060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6061_ = l_Lean_Server_chainLspRequestHandler___redArg(
        v_method_6055_,
        v_inst_6056_,
        v_inst_6057_,
        v_inst_6058_,
        v_handler_6059_,
    );
    return v_res_6061_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler(
    mut v_method_6062_: *mut crate::leanh::LeanObject,
    mut v_paramType_6063_: *mut crate::leanh::LeanObject,
    mut v_inst_6064_: *mut crate::leanh::LeanObject,
    mut v_respType_6065_: *mut crate::leanh::LeanObject,
    mut v_inst_6066_: *mut crate::leanh::LeanObject,
    mut v_inst_6067_: *mut crate::leanh::LeanObject,
    mut v_handler_6068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6070_ = l_Lean_Server_chainLspRequestHandler___redArg(
        v_method_6062_,
        v_inst_6064_,
        v_inst_6066_,
        v_inst_6067_,
        v_handler_6068_,
    );
    return v___x_6070_;
}
pub unsafe fn l_Lean_Server_chainLspRequestHandler___boxed(
    mut v_method_6071_: *mut crate::leanh::LeanObject,
    mut v_paramType_6072_: *mut crate::leanh::LeanObject,
    mut v_inst_6073_: *mut crate::leanh::LeanObject,
    mut v_respType_6074_: *mut crate::leanh::LeanObject,
    mut v_inst_6075_: *mut crate::leanh::LeanObject,
    mut v_inst_6076_: *mut crate::leanh::LeanObject,
    mut v_handler_6077_: *mut crate::leanh::LeanObject,
    mut v_a_6078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6079_ = l_Lean_Server_chainLspRequestHandler(
        v_method_6071_,
        v_paramType_6072_,
        v_inst_6073_,
        v_respType_6074_,
        v_inst_6075_,
        v_inst_6076_,
        v_handler_6077_,
    );
    return v_res_6079_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_ctorIdx(
    mut v_x_6080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6080_) == 0 {
        let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6081_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_6081_;
    } else {
        let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6082_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_6082_;
    }
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(
    mut v_x_6083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6084_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_6083_);
    crate::leanh::lean_dec(v_x_6083_);
    return v_res_6084_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(
    mut v_t_6085_: *mut crate::leanh::LeanObject,
    mut v_k_6086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_6085_) == 0 {
        return v_k_6086_;
    } else {
        let mut v_refreshMethod_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_refreshIntervalMs_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_refreshMethod_6087_ = crate::leanh::lean_ctor_get(v_t_6085_, 0);
        crate::leanh::lean_inc_ref(v_refreshMethod_6087_);
        v_refreshIntervalMs_6088_ = crate::leanh::lean_ctor_get(v_t_6085_, 1);
        crate::leanh::lean_inc(v_refreshIntervalMs_6088_);
        crate::leanh::lean_dec_ref_known(v_t_6085_, 2);
        v___x_6089_ =
            crate::leanh::lean_apply_2(v_k_6086_, v_refreshMethod_6087_, v_refreshIntervalMs_6088_);
        return v___x_6089_;
    }
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_ctorElim(
    mut v_motive_6090_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6091_: *mut crate::leanh::LeanObject,
    mut v_t_6092_: *mut crate::leanh::LeanObject,
    mut v_h_6093_: *mut crate::leanh::LeanObject,
    mut v_k_6094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6095_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_6092_, v_k_6094_);
    return v___x_6095_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(
    mut v_motive_6096_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6097_: *mut crate::leanh::LeanObject,
    mut v_t_6098_: *mut crate::leanh::LeanObject,
    mut v_h_6099_: *mut crate::leanh::LeanObject,
    mut v_k_6100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6101_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(
        v_motive_6096_,
        v_ctorIdx_6097_,
        v_t_6098_,
        v_h_6099_,
        v_k_6100_,
    );
    crate::leanh::lean_dec(v_ctorIdx_6097_);
    return v_res_6101_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(
    mut v_t_6102_: *mut crate::leanh::LeanObject,
    mut v_complete_6103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6104_ =
        l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_6102_, v_complete_6103_);
    return v___x_6104_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_complete_elim(
    mut v_motive_6105_: *mut crate::leanh::LeanObject,
    mut v_t_6106_: *mut crate::leanh::LeanObject,
    mut v_h_6107_: *mut crate::leanh::LeanObject,
    mut v_complete_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6109_ =
        l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_6106_, v_complete_6108_);
    return v___x_6109_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(
    mut v_t_6110_: *mut crate::leanh::LeanObject,
    mut v_partial_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6112_ =
        l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_6110_, v_partial_6111_);
    return v___x_6112_;
}
pub unsafe fn l_Lean_Server_RequestHandlerCompleteness_partial_elim(
    mut v_motive_6113_: *mut crate::leanh::LeanObject,
    mut v_t_6114_: *mut crate::leanh::LeanObject,
    mut v_h_6115_: *mut crate::leanh::LeanObject,
    mut v_partial_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6117_ =
        l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_6114_, v_partial_6116_);
    return v___x_6117_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6118_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6119_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
    v___x_6120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6120_, 0, v___x_6119_);
    return v___x_6120_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6122_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
    v___x_6123_ = lean_st_mk_ref(v___x_6122_);
    v___x_6124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6124_, 0, v___x_6123_);
    return v___x_6124_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(
    mut v_a_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6126_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
    return v_res_6126_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
    mut v_method_6128_: *mut crate::leanh::LeanObject,
    mut v_state_6129_: *mut crate::leanh::LeanObject,
    mut v_inst_6130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6136_: u8 = 0;
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6140_: u8 = 0;
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6132_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_state_6129_,
                    v_inst_6130_,
                );
                if crate::leanh::lean_obj_tag(v___x_6132_) == 1 {
                    v_val_6133_ = crate::leanh::lean_ctor_get(v___x_6132_, 0);
                    v_isSharedCheck_6140_ = (!crate::leanh::lean_is_exclusive(v___x_6132_)) as u8;
                    if v_isSharedCheck_6140_ == 0 {
                        v___x_6135_ = v___x_6132_;
                        v_isShared_6136_ = v_isSharedCheck_6140_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6133_);
                        crate::leanh::lean_dec(v___x_6132_);
                        v___x_6135_ = crate::leanh::lean_box(0);
                        v_isShared_6136_ = v_isSharedCheck_6140_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6132_);
                    v___x_6141_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0;
                    v___x_6142_ = lean_string_append(v___x_6141_, v_method_6128_);
                    v___x_6143_ = l_Lean_Server_RequestError_internalError(v___x_6142_);
                    v___x_6144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6144_, 0, v___x_6143_);
                    return v___x_6144_;
                }
            }
            1 => {
                if v_isShared_6136_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6135_, 0);
                    v___x_6138_ = v___x_6135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_val_6133_);
                    v___x_6138_ = v_reuseFailAlloc_6139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(
    mut v_method_6145_: *mut crate::leanh::LeanObject,
    mut v_state_6146_: *mut crate::leanh::LeanObject,
    mut v_inst_6147_: *mut crate::leanh::LeanObject,
    mut v_a_6148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6149_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
        v_method_6145_,
        v_state_6146_,
        v_inst_6147_,
    );
    crate::leanh::lean_dec(v_inst_6147_);
    crate::leanh::lean_dec(v_state_6146_);
    crate::leanh::lean_dec_ref(v_method_6145_);
    return v_res_6149_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(
    mut v_method_6150_: *mut crate::leanh::LeanObject,
    mut v_state_6151_: *mut crate::leanh::LeanObject,
    mut v_stateType_6152_: *mut crate::leanh::LeanObject,
    mut v_inst_6153_: *mut crate::leanh::LeanObject,
    mut v_a_6154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6156_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
        v_method_6150_,
        v_state_6151_,
        v_inst_6153_,
    );
    return v___x_6156_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(
    mut v_method_6157_: *mut crate::leanh::LeanObject,
    mut v_state_6158_: *mut crate::leanh::LeanObject,
    mut v_stateType_6159_: *mut crate::leanh::LeanObject,
    mut v_inst_6160_: *mut crate::leanh::LeanObject,
    mut v_a_6161_: *mut crate::leanh::LeanObject,
    mut v_a_6162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6163_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(
        v_method_6157_,
        v_state_6158_,
        v_stateType_6159_,
        v_inst_6160_,
        v_a_6161_,
    );
    crate::leanh::lean_dec_ref(v_a_6161_);
    crate::leanh::lean_dec(v_inst_6160_);
    crate::leanh::lean_dec(v_state_6158_);
    crate::leanh::lean_dec_ref(v_method_6157_);
    return v_res_6163_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(
    mut v_method_6164_: *mut crate::leanh::LeanObject,
    mut v_state_6165_: *mut crate::leanh::LeanObject,
    mut v_inst_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6172_: u8 = 0;
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6176_: u8 = 0;
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6168_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_state_6165_,
                    v_inst_6166_,
                );
                if crate::leanh::lean_obj_tag(v___x_6168_) == 1 {
                    v_val_6169_ = crate::leanh::lean_ctor_get(v___x_6168_, 0);
                    v_isSharedCheck_6176_ = (!crate::leanh::lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6176_ == 0 {
                        v___x_6171_ = v___x_6168_;
                        v_isShared_6172_ = v_isSharedCheck_6176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6169_);
                        crate::leanh::lean_dec(v___x_6168_);
                        v___x_6171_ = crate::leanh::lean_box(0);
                        v_isShared_6172_ = v_isSharedCheck_6176_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6168_);
                    v___x_6177_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0;
                    v___x_6178_ = lean_string_append(v___x_6177_, v_method_6164_);
                    v___x_6179_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6179_, 0, v___x_6178_);
                    v___x_6180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6180_, 0, v___x_6179_);
                    return v___x_6180_;
                }
            }
            1 => {
                if v_isShared_6172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6171_, 0);
                    v___x_6174_ = v___x_6171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6175_, 0, v_val_6169_);
                    v___x_6174_ = v_reuseFailAlloc_6175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(
    mut v_method_6181_: *mut crate::leanh::LeanObject,
    mut v_state_6182_: *mut crate::leanh::LeanObject,
    mut v_inst_6183_: *mut crate::leanh::LeanObject,
    mut v_a_6184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6185_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(
        v_method_6181_,
        v_state_6182_,
        v_inst_6183_,
    );
    crate::leanh::lean_dec(v_inst_6183_);
    crate::leanh::lean_dec(v_state_6182_);
    crate::leanh::lean_dec_ref(v_method_6181_);
    return v_res_6185_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(
    mut v_method_6186_: *mut crate::leanh::LeanObject,
    mut v_state_6187_: *mut crate::leanh::LeanObject,
    mut v_stateType_6188_: *mut crate::leanh::LeanObject,
    mut v_inst_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6191_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(
        v_method_6186_,
        v_state_6187_,
        v_inst_6189_,
    );
    return v___x_6191_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(
    mut v_method_6192_: *mut crate::leanh::LeanObject,
    mut v_state_6193_: *mut crate::leanh::LeanObject,
    mut v_stateType_6194_: *mut crate::leanh::LeanObject,
    mut v_inst_6195_: *mut crate::leanh::LeanObject,
    mut v_a_6196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6197_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(
        v_method_6192_,
        v_state_6193_,
        v_stateType_6194_,
        v_inst_6195_,
    );
    crate::leanh::lean_dec(v_inst_6195_);
    crate::leanh::lean_dec(v_state_6193_);
    crate::leanh::lean_dec_ref(v_method_6192_);
    return v_res_6197_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(
    mut v_inst_6198_: *mut crate::leanh::LeanObject,
    mut v_method_6199_: *mut crate::leanh::LeanObject,
    mut v_inst_6200_: *mut crate::leanh::LeanObject,
    mut v_handler_6201_: *mut crate::leanh::LeanObject,
    mut v_inst_6202_: *mut crate::leanh::LeanObject,
    mut v_param_6203_: *mut crate::leanh::LeanObject,
    mut v_state_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6215_: u8 = 0;
    let mut v_fst_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6220_: u8 = 0;
    let mut v_response_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isComplete_6222_: u8 = 0;
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6234_: u8 = 0;
    let mut v_isSharedCheck_6235_: u8 = 0;
    let mut v_a_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6239_: u8 = 0;
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6243_: u8 = 0;
    let mut v_a_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6251_: u8 = 0;
    let mut v_a_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6207_ =
                    l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_6198_, v_param_6203_);
                if crate::leanh::lean_obj_tag(v___x_6207_) == 0 {
                    v_a_6208_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                    crate::leanh::lean_inc(v_a_6208_);
                    crate::leanh::lean_dec_ref_known(v___x_6207_, 1);
                    v___x_6209_ =
                        l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
                            v_method_6199_,
                            v_state_6204_,
                            v_inst_6200_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6209_) == 0 {
                        v_a_6210_ = crate::leanh::lean_ctor_get(v___x_6209_, 0);
                        crate::leanh::lean_inc(v_a_6210_);
                        crate::leanh::lean_dec_ref_known(v___x_6209_, 1);
                        crate::leanh::lean_inc_ref(v___y_6205_);
                        v___x_6211_ = crate::leanh::lean_apply_4(
                            v_handler_6201_,
                            v_a_6208_,
                            v_a_6210_,
                            v___y_6205_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6211_) == 0 {
                            v_a_6212_ = crate::leanh::lean_ctor_get(v___x_6211_, 0);
                            v_isSharedCheck_6235_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6211_)) as u8;
                            if v_isSharedCheck_6235_ == 0 {
                                v___x_6214_ = v___x_6211_;
                                v_isShared_6215_ = v_isSharedCheck_6235_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6212_);
                                crate::leanh::lean_dec(v___x_6211_);
                                v___x_6214_ = crate::leanh::lean_box(0);
                                v_isShared_6215_ = v_isSharedCheck_6235_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_inst_6202_);
                            crate::leanh::lean_dec(v_inst_6200_);
                            v_a_6236_ = crate::leanh::lean_ctor_get(v___x_6211_, 0);
                            v_isSharedCheck_6243_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6211_)) as u8;
                            if v_isSharedCheck_6243_ == 0 {
                                v___x_6238_ = v___x_6211_;
                                v_isShared_6239_ = v_isSharedCheck_6243_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6236_);
                                crate::leanh::lean_dec(v___x_6211_);
                                v___x_6238_ = crate::leanh::lean_box(0);
                                v_isShared_6239_ = v_isSharedCheck_6243_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6208_);
                        crate::leanh::lean_dec_ref(v_inst_6202_);
                        crate::leanh::lean_dec_ref(v_handler_6201_);
                        crate::leanh::lean_dec(v_inst_6200_);
                        v_a_6244_ = crate::leanh::lean_ctor_get(v___x_6209_, 0);
                        v_isSharedCheck_6251_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6209_)) as u8;
                        if v_isSharedCheck_6251_ == 0 {
                            v___x_6246_ = v___x_6209_;
                            v_isShared_6247_ = v_isSharedCheck_6251_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6244_);
                            crate::leanh::lean_dec(v___x_6209_);
                            v___x_6246_ = crate::leanh::lean_box(0);
                            v_isShared_6247_ = v_isSharedCheck_6251_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_6202_);
                    crate::leanh::lean_dec_ref(v_handler_6201_);
                    crate::leanh::lean_dec(v_inst_6200_);
                    v_a_6252_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                    v_isSharedCheck_6259_ = (!crate::leanh::lean_is_exclusive(v___x_6207_)) as u8;
                    if v_isSharedCheck_6259_ == 0 {
                        v___x_6254_ = v___x_6207_;
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6252_);
                        crate::leanh::lean_dec(v___x_6207_);
                        v___x_6254_ = crate::leanh::lean_box(0);
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6216_ = crate::leanh::lean_ctor_get(v_a_6212_, 0);
                v_snd_6217_ = crate::leanh::lean_ctor_get(v_a_6212_, 1);
                v_isSharedCheck_6234_ = (!crate::leanh::lean_is_exclusive(v_a_6212_)) as u8;
                if v_isSharedCheck_6234_ == 0 {
                    v___x_6219_ = v_a_6212_;
                    v_isShared_6220_ = v_isSharedCheck_6234_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6217_);
                    crate::leanh::lean_inc(v_fst_6216_);
                    crate::leanh::lean_dec(v_a_6212_);
                    v___x_6219_ = crate::leanh::lean_box(0);
                    v_isShared_6220_ = v_isSharedCheck_6234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_response_6221_ = crate::leanh::lean_ctor_get(v_fst_6216_, 0);
                crate::leanh::lean_inc(v_response_6221_);
                v_isComplete_6222_ = crate::leanh::lean_ctor_get_uint8(
                    v_fst_6216_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec(v_fst_6216_);
                v___x_6223_ = crate::leanh::lean_apply_1(v_inst_6202_, v_response_6221_);
                crate::leanh::lean_inc(v___x_6223_);
                v___x_6224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6224_, 0, v___x_6223_);
                v___x_6225_ = l_Lean_Json_compress(v___x_6223_);
                v___x_6226_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6226_, 0, v___x_6224_);
                crate::leanh::lean_ctor_set(v___x_6226_, 1, v___x_6225_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_isComplete_6222_,
                );
                if v_isShared_6220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6219_, 0, v_inst_6200_);
                    v___x_6228_ = v___x_6219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6233_, 0, v_inst_6200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6233_, 1, v_snd_6217_);
                    v___x_6228_ = v_reuseFailAlloc_6233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6229_, 0, v___x_6226_);
                crate::leanh::lean_ctor_set(v___x_6229_, 1, v___x_6228_);
                if v_isShared_6215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6214_, 0, v___x_6229_);
                    v___x_6231_ = v___x_6214_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6232_, 0, v___x_6229_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6231_;
            }
            5 => {
                if v_isShared_6239_ == 0 {
                    v___x_6241_ = v___x_6238_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_a_6236_);
                    v___x_6241_ = v_reuseFailAlloc_6242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6241_;
            }
            7 => {
                if v_isShared_6247_ == 0 {
                    v___x_6249_ = v___x_6246_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
                    v___x_6249_ = v_reuseFailAlloc_6250_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6249_;
            }
            9 => {
                if v_isShared_6255_ == 0 {
                    v___x_6257_ = v___x_6254_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_a_6252_);
                    v___x_6257_ = v_reuseFailAlloc_6258_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(
    mut v_inst_6260_: *mut crate::leanh::LeanObject,
    mut v_method_6261_: *mut crate::leanh::LeanObject,
    mut v_inst_6262_: *mut crate::leanh::LeanObject,
    mut v_handler_6263_: *mut crate::leanh::LeanObject,
    mut v_inst_6264_: *mut crate::leanh::LeanObject,
    mut v_param_6265_: *mut crate::leanh::LeanObject,
    mut v_state_6266_: *mut crate::leanh::LeanObject,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6269_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_6260_, v_method_6261_, v_inst_6262_, v_handler_6263_, v_inst_6264_, v_param_6265_, v_state_6266_, v___y_6267_);
    crate::leanh::lean_dec_ref(v___y_6267_);
    crate::leanh::lean_dec(v_state_6266_);
    crate::leanh::lean_dec_ref(v_method_6261_);
    return v_res_6269_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(
    mut v_method_6270_: *mut crate::leanh::LeanObject,
    mut v_inst_6271_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6272_: *mut crate::leanh::LeanObject,
    mut v_param_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v_snd_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6296_: u8 = 0;
    let mut v_unused_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6298_: u8 = 0;
    let mut v_a_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6302_: u8 = 0;
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6306_: u8 = 0;
    let mut v_a_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6277_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
                    v_method_6270_,
                    v___y_6274_,
                    v_inst_6271_,
                );
                if crate::leanh::lean_obj_tag(v___x_6277_) == 0 {
                    v_a_6278_ = crate::leanh::lean_ctor_get(v___x_6277_, 0);
                    crate::leanh::lean_inc(v_a_6278_);
                    crate::leanh::lean_dec_ref_known(v___x_6277_, 1);
                    crate::leanh::lean_inc_ref(v___y_6275_);
                    v___x_6279_ = crate::leanh::lean_apply_4(
                        v_onDidChange_6272_,
                        v_param_6273_,
                        v_a_6278_,
                        v___y_6275_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6279_) == 0 {
                        v_a_6280_ = crate::leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6298_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6298_ == 0 {
                            v___x_6282_ = v___x_6279_;
                            v_isShared_6283_ = v_isSharedCheck_6298_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6280_);
                            crate::leanh::lean_dec(v___x_6279_);
                            v___x_6282_ = crate::leanh::lean_box(0);
                            v_isShared_6283_ = v_isSharedCheck_6298_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_inst_6271_);
                        v_a_6299_ = crate::leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6306_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6306_ == 0 {
                            v___x_6301_ = v___x_6279_;
                            v_isShared_6302_ = v_isSharedCheck_6306_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6299_);
                            crate::leanh::lean_dec(v___x_6279_);
                            v___x_6301_ = crate::leanh::lean_box(0);
                            v_isShared_6302_ = v_isSharedCheck_6306_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_param_6273_);
                    crate::leanh::lean_dec_ref(v_onDidChange_6272_);
                    crate::leanh::lean_dec(v_inst_6271_);
                    v_a_6307_ = crate::leanh::lean_ctor_get(v___x_6277_, 0);
                    v_isSharedCheck_6314_ = (!crate::leanh::lean_is_exclusive(v___x_6277_)) as u8;
                    if v_isSharedCheck_6314_ == 0 {
                        v___x_6309_ = v___x_6277_;
                        v_isShared_6310_ = v_isSharedCheck_6314_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6307_);
                        crate::leanh::lean_dec(v___x_6277_);
                        v___x_6309_ = crate::leanh::lean_box(0);
                        v_isShared_6310_ = v_isSharedCheck_6314_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6284_ = crate::leanh::lean_ctor_get(v_a_6280_, 1);
                v_isSharedCheck_6296_ = (!crate::leanh::lean_is_exclusive(v_a_6280_)) as u8;
                if v_isSharedCheck_6296_ == 0 {
                    v_unused_6297_ = crate::leanh::lean_ctor_get(v_a_6280_, 0);
                    crate::leanh::lean_dec(v_unused_6297_);
                    v___x_6286_ = v_a_6280_;
                    v_isShared_6287_ = v_isSharedCheck_6296_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6284_);
                    crate::leanh::lean_dec(v_a_6280_);
                    v___x_6286_ = crate::leanh::lean_box(0);
                    v_isShared_6287_ = v_isSharedCheck_6296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6286_, 0, v_inst_6271_);
                    v___x_6289_ = v___x_6286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6295_, 0, v_inst_6271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6295_, 1, v_snd_6284_);
                    v___x_6289_ = v_reuseFailAlloc_6295_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6290_ = crate::leanh::lean_box(0);
                v___x_6291_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6291_, 0, v___x_6290_);
                crate::leanh::lean_ctor_set(v___x_6291_, 1, v___x_6289_);
                if v_isShared_6283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6282_, 0, v___x_6291_);
                    v___x_6293_ = v___x_6282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6294_, 0, v___x_6291_);
                    v___x_6293_ = v_reuseFailAlloc_6294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6293_;
            }
            5 => {
                if v_isShared_6302_ == 0 {
                    v___x_6304_ = v___x_6301_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_a_6299_);
                    v___x_6304_ = v_reuseFailAlloc_6305_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6304_;
            }
            7 => {
                if v_isShared_6310_ == 0 {
                    v___x_6312_ = v___x_6309_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6313_, 0, v_a_6307_);
                    v___x_6312_ = v_reuseFailAlloc_6313_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(
    mut v_method_6315_: *mut crate::leanh::LeanObject,
    mut v_inst_6316_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6317_: *mut crate::leanh::LeanObject,
    mut v_param_6318_: *mut crate::leanh::LeanObject,
    mut v___y_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6322_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_6315_, v_inst_6316_, v_onDidChange_6317_, v_param_6318_, v___y_6319_, v___y_6320_);
    crate::leanh::lean_dec_ref(v___y_6320_);
    crate::leanh::lean_dec(v___y_6319_);
    crate::leanh::lean_dec_ref(v_method_6315_);
    return v_res_6322_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(
    mut v___x_6323_: *mut crate::leanh::LeanObject,
    mut v_x_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    return v___x_6323_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(
    mut v___x_6325_: *mut crate::leanh::LeanObject,
    mut v_x_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6327_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_6325_, v_x_6326_);
    crate::leanh::lean_dec_ref(v_x_6326_);
    return v_res_6327_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(
    mut v___x_6328_: *mut crate::leanh::LeanObject,
    mut v_x_6329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    return v___x_6328_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(
    mut v___x_6330_: *mut crate::leanh::LeanObject,
    mut v_x_6331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6332_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_6330_, v_x_6331_);
    crate::leanh::lean_dec_ref(v_x_6331_);
    return v_res_6332_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(
    mut v_val_6333_: *mut crate::leanh::LeanObject,
    mut v___f_6334_: *mut crate::leanh::LeanObject,
    mut v_param_6335_: *mut crate::leanh::LeanObject,
    mut v_x_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6344_: u8 = 0;
    let mut v_fst_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6351_: u8 = 0;
    let mut v_a_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6355_: u8 = 0;
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6339_ = lean_st_ref_get(v_val_6333_);
                crate::leanh::lean_inc_ref(v___y_6337_);
                v___x_6340_ = crate::leanh::lean_apply_4(
                    v___f_6334_,
                    v_param_6335_,
                    v___x_6339_,
                    v___y_6337_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6340_) == 0 {
                    v_a_6341_ = crate::leanh::lean_ctor_get(v___x_6340_, 0);
                    v_isSharedCheck_6351_ = (!crate::leanh::lean_is_exclusive(v___x_6340_)) as u8;
                    if v_isSharedCheck_6351_ == 0 {
                        v___x_6343_ = v___x_6340_;
                        v_isShared_6344_ = v_isSharedCheck_6351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6341_);
                        crate::leanh::lean_dec(v___x_6340_);
                        v___x_6343_ = crate::leanh::lean_box(0);
                        v_isShared_6344_ = v_isSharedCheck_6351_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6352_ = crate::leanh::lean_ctor_get(v___x_6340_, 0);
                    v_isSharedCheck_6359_ = (!crate::leanh::lean_is_exclusive(v___x_6340_)) as u8;
                    if v_isSharedCheck_6359_ == 0 {
                        v___x_6354_ = v___x_6340_;
                        v_isShared_6355_ = v_isSharedCheck_6359_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6352_);
                        crate::leanh::lean_dec(v___x_6340_);
                        v___x_6354_ = crate::leanh::lean_box(0);
                        v_isShared_6355_ = v_isSharedCheck_6359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6345_ = crate::leanh::lean_ctor_get(v_a_6341_, 0);
                crate::leanh::lean_inc(v_fst_6345_);
                v_snd_6346_ = crate::leanh::lean_ctor_get(v_a_6341_, 1);
                crate::leanh::lean_inc(v_snd_6346_);
                crate::leanh::lean_dec(v_a_6341_);
                v___x_6347_ = lean_st_ref_set(v_val_6333_, v_snd_6346_);
                if v_isShared_6344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6343_, 0, v_fst_6345_);
                    v___x_6349_ = v___x_6343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_fst_6345_);
                    v___x_6349_ = v_reuseFailAlloc_6350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6349_;
            }
            3 => {
                if v_isShared_6355_ == 0 {
                    v___x_6357_ = v___x_6354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6358_, 0, v_a_6352_);
                    v___x_6357_ = v_reuseFailAlloc_6358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(
    mut v_val_6360_: *mut crate::leanh::LeanObject,
    mut v___f_6361_: *mut crate::leanh::LeanObject,
    mut v_param_6362_: *mut crate::leanh::LeanObject,
    mut v_x_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6366_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_6360_, v___f_6361_, v_param_6362_, v_x_6363_, v___y_6364_);
    crate::leanh::lean_dec_ref(v___y_6364_);
    crate::leanh::lean_dec(v_val_6360_);
    return v_res_6366_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(
    mut v___f_6367_: *mut crate::leanh::LeanObject,
    mut v___f_6368_: *mut crate::leanh::LeanObject,
    mut v_lastTask_6369_: *mut crate::leanh::LeanObject,
    mut v___y_6370_: *mut crate::leanh::LeanObject,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6377_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6373_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(
                    v_lastTask_6369_,
                    v___f_6367_,
                    v___y_6371_,
                );
                v_a_6374_ = crate::leanh::lean_ctor_get(v___x_6373_, 0);
                v_isSharedCheck_6383_ = (!crate::leanh::lean_is_exclusive(v___x_6373_)) as u8;
                if v_isSharedCheck_6383_ == 0 {
                    v___x_6376_ = v___x_6373_;
                    v_isShared_6377_ = v_isSharedCheck_6383_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6374_);
                    crate::leanh::lean_dec(v___x_6373_);
                    v___x_6376_ = crate::leanh::lean_box(0);
                    v_isShared_6377_ = v_isSharedCheck_6383_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_6374_);
                v___x_6378_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_6368_, v_a_6374_);
                v___x_6379_ = lean_st_ref_set(v___y_6370_, v___x_6378_);
                if v_isShared_6377_ == 0 {
                    v___x_6381_ = v___x_6376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6374_);
                    v___x_6381_ = v_reuseFailAlloc_6382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(
    mut v___f_6384_: *mut crate::leanh::LeanObject,
    mut v___f_6385_: *mut crate::leanh::LeanObject,
    mut v_lastTask_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_6384_, v___f_6385_, v_lastTask_6386_, v___y_6387_, v___y_6388_);
    crate::leanh::lean_dec_ref(v___y_6388_);
    crate::leanh::lean_dec(v___y_6387_);
    return v_res_6390_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(
    mut v_val_6391_: *mut crate::leanh::LeanObject,
    mut v___f_6392_: *mut crate::leanh::LeanObject,
    mut v___f_6393_: *mut crate::leanh::LeanObject,
    mut v___f_6394_: *mut crate::leanh::LeanObject,
    mut v___x_6395_: *mut crate::leanh::LeanObject,
    mut v___f_6396_: *mut crate::leanh::LeanObject,
    mut v___f_6397_: *mut crate::leanh::LeanObject,
    mut v_val_6398_: *mut crate::leanh::LeanObject,
    mut v_param_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410__overap_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6402_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___f_6402_, 0, v_val_6391_);
    crate::leanh::lean_closure_set(v___f_6402_, 1, v___f_6392_);
    crate::leanh::lean_closure_set(v___f_6402_, 2, v_param_6399_);
    v___f_6403_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_6403_, 0, v___f_6402_);
    crate::leanh::lean_closure_set(v___f_6403_, 1, v___f_6393_);
    v___x_6404_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_6404_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6404_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6404_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6404_, 3, v___f_6394_);
    crate::leanh::lean_inc_ref(v___x_6395_);
    v___x_6405_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_6405_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6405_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6405_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6405_, 3, v___x_6395_);
    crate::leanh::lean_closure_set(v___x_6405_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6405_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6405_, 6, v___x_6404_);
    crate::leanh::lean_closure_set(v___x_6405_, 7, v___f_6403_);
    v___x_6410__overap_6406_ = l_Std_Mutex_atomically___redArg(
        v___x_6395_,
        v___f_6396_,
        v___f_6397_,
        v_val_6398_,
        v___x_6405_,
    );
    crate::leanh::lean_inc_ref(v___y_6400_);
    v___x_6407_ = crate::leanh::lean_apply_2(
        v___x_6410__overap_6406_,
        v___y_6400_,
        crate::leanh::lean_box(0),
    );
    return v___x_6407_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(
    mut v_val_6408_: *mut crate::leanh::LeanObject,
    mut v___f_6409_: *mut crate::leanh::LeanObject,
    mut v___f_6410_: *mut crate::leanh::LeanObject,
    mut v___f_6411_: *mut crate::leanh::LeanObject,
    mut v___x_6412_: *mut crate::leanh::LeanObject,
    mut v___f_6413_: *mut crate::leanh::LeanObject,
    mut v___f_6414_: *mut crate::leanh::LeanObject,
    mut v_val_6415_: *mut crate::leanh::LeanObject,
    mut v_param_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6419_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_6408_, v___f_6409_, v___f_6410_, v___f_6411_, v___x_6412_, v___f_6413_, v___f_6414_, v_val_6415_, v_param_6416_, v___y_6417_);
    crate::leanh::lean_dec_ref(v___y_6417_);
    return v_res_6419_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(
    mut v_val_6420_: *mut crate::leanh::LeanObject,
    mut v___f_6421_: *mut crate::leanh::LeanObject,
    mut v_param_6422_: *mut crate::leanh::LeanObject,
    mut v_x_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6431_: u8 = 0;
    let mut v_snd_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6437_: u8 = 0;
    let mut v_a_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6426_ = lean_st_ref_get(v_val_6420_);
                crate::leanh::lean_inc_ref(v___y_6424_);
                v___x_6427_ = crate::leanh::lean_apply_4(
                    v___f_6421_,
                    v_param_6422_,
                    v___x_6426_,
                    v___y_6424_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6427_) == 0 {
                    v_a_6428_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                    v_isSharedCheck_6437_ = (!crate::leanh::lean_is_exclusive(v___x_6427_)) as u8;
                    if v_isSharedCheck_6437_ == 0 {
                        v___x_6430_ = v___x_6427_;
                        v_isShared_6431_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6428_);
                        crate::leanh::lean_dec(v___x_6427_);
                        v___x_6430_ = crate::leanh::lean_box(0);
                        v_isShared_6431_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6438_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                    v_isSharedCheck_6445_ = (!crate::leanh::lean_is_exclusive(v___x_6427_)) as u8;
                    if v_isSharedCheck_6445_ == 0 {
                        v___x_6440_ = v___x_6427_;
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6438_);
                        crate::leanh::lean_dec(v___x_6427_);
                        v___x_6440_ = crate::leanh::lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6432_ = crate::leanh::lean_ctor_get(v_a_6428_, 1);
                crate::leanh::lean_inc(v_snd_6432_);
                crate::leanh::lean_dec(v_a_6428_);
                v___x_6433_ = lean_st_ref_set(v_val_6420_, v_snd_6432_);
                if v_isShared_6431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6430_, 0, v___x_6433_);
                    v___x_6435_ = v___x_6430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6436_, 0, v___x_6433_);
                    v___x_6435_ = v_reuseFailAlloc_6436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6435_;
            }
            3 => {
                if v_isShared_6441_ == 0 {
                    v___x_6443_ = v___x_6440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
                    v___x_6443_ = v_reuseFailAlloc_6444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(
    mut v_val_6446_: *mut crate::leanh::LeanObject,
    mut v___f_6447_: *mut crate::leanh::LeanObject,
    mut v_param_6448_: *mut crate::leanh::LeanObject,
    mut v_x_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6452_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_6446_, v___f_6447_, v_param_6448_, v_x_6449_, v___y_6450_);
    crate::leanh::lean_dec_ref(v___y_6450_);
    crate::leanh::lean_dec(v_val_6446_);
    return v_res_6452_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(
    mut v___f_6453_: *mut crate::leanh::LeanObject,
    mut v___f_6454_: *mut crate::leanh::LeanObject,
    mut v_lastTask_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6463_: u8 = 0;
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6459_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(
                    v_lastTask_6455_,
                    v___f_6453_,
                    v___y_6457_,
                );
                v_a_6460_ = crate::leanh::lean_ctor_get(v___x_6459_, 0);
                v_isSharedCheck_6469_ = (!crate::leanh::lean_is_exclusive(v___x_6459_)) as u8;
                if v_isSharedCheck_6469_ == 0 {
                    v___x_6462_ = v___x_6459_;
                    v_isShared_6463_ = v_isSharedCheck_6469_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6460_);
                    crate::leanh::lean_dec(v___x_6459_);
                    v___x_6462_ = crate::leanh::lean_box(0);
                    v_isShared_6463_ = v_isSharedCheck_6469_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6464_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_6454_, v_a_6460_);
                v___x_6465_ = lean_st_ref_set(v___y_6456_, v___x_6464_);
                if v_isShared_6463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6462_, 0, v___x_6465_);
                    v___x_6467_ = v___x_6462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6468_, 0, v___x_6465_);
                    v___x_6467_ = v_reuseFailAlloc_6468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(
    mut v___f_6470_: *mut crate::leanh::LeanObject,
    mut v___f_6471_: *mut crate::leanh::LeanObject,
    mut v_lastTask_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
    mut v___y_6475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6476_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_6470_, v___f_6471_, v_lastTask_6472_, v___y_6473_, v___y_6474_);
    crate::leanh::lean_dec_ref(v___y_6474_);
    crate::leanh::lean_dec(v___y_6473_);
    return v_res_6476_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(
    mut v_val_6477_: *mut crate::leanh::LeanObject,
    mut v___f_6478_: *mut crate::leanh::LeanObject,
    mut v___f_6479_: *mut crate::leanh::LeanObject,
    mut v___f_6480_: *mut crate::leanh::LeanObject,
    mut v___x_6481_: *mut crate::leanh::LeanObject,
    mut v___f_6482_: *mut crate::leanh::LeanObject,
    mut v___f_6483_: *mut crate::leanh::LeanObject,
    mut v_val_6484_: *mut crate::leanh::LeanObject,
    mut v_param_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461__overap_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6488_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___f_6488_, 0, v_val_6477_);
    crate::leanh::lean_closure_set(v___f_6488_, 1, v___f_6478_);
    crate::leanh::lean_closure_set(v___f_6488_, 2, v_param_6485_);
    v___f_6489_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___f_6489_, 0, v___f_6488_);
    crate::leanh::lean_closure_set(v___f_6489_, 1, v___f_6479_);
    v___x_6490_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_6490_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6490_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6490_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6490_, 3, v___f_6480_);
    crate::leanh::lean_inc_ref(v___x_6481_);
    v___x_6491_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_6491_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6491_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6491_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6491_, 3, v___x_6481_);
    crate::leanh::lean_closure_set(v___x_6491_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6491_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6491_, 6, v___x_6490_);
    crate::leanh::lean_closure_set(v___x_6491_, 7, v___f_6489_);
    v___x_6461__overap_6492_ = l_Std_Mutex_atomically___redArg(
        v___x_6481_,
        v___f_6482_,
        v___f_6483_,
        v_val_6484_,
        v___x_6491_,
    );
    crate::leanh::lean_inc_ref(v___y_6486_);
    v___x_6493_ = crate::leanh::lean_apply_2(
        v___x_6461__overap_6492_,
        v___y_6486_,
        crate::leanh::lean_box(0),
    );
    return v___x_6493_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(
    mut v_val_6494_: *mut crate::leanh::LeanObject,
    mut v___f_6495_: *mut crate::leanh::LeanObject,
    mut v___f_6496_: *mut crate::leanh::LeanObject,
    mut v___f_6497_: *mut crate::leanh::LeanObject,
    mut v___x_6498_: *mut crate::leanh::LeanObject,
    mut v___f_6499_: *mut crate::leanh::LeanObject,
    mut v___f_6500_: *mut crate::leanh::LeanObject,
    mut v_val_6501_: *mut crate::leanh::LeanObject,
    mut v_param_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6505_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_6494_, v___f_6495_, v___f_6496_, v___f_6497_, v___x_6498_, v___f_6499_, v___f_6500_, v_val_6501_, v_param_6502_, v___y_6503_);
    crate::leanh::lean_dec_ref(v___y_6503_);
    return v_res_6505_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6506_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_6506_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
    v___x_6508_ = l_ReaderT_instMonad___redArg(v___x_6507_);
    return v___x_6508_;
}
pub unsafe fn _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6510_ = crate::leanh::lean_box(0);
    v___x_6511_ = lean_task_pure(v___x_6510_);
    return v___x_6511_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(
    mut v_method_6537_: *mut crate::leanh::LeanObject,
    mut v_completeness_6538_: *mut crate::leanh::LeanObject,
    mut v_inst_6539_: *mut crate::leanh::LeanObject,
    mut v_inst_6540_: *mut crate::leanh::LeanObject,
    mut v_inst_6541_: *mut crate::leanh::LeanObject,
    mut v_inst_6542_: *mut crate::leanh::LeanObject,
    mut v_initState_6543_: *mut crate::leanh::LeanObject,
    mut v_handler_6544_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6552_: u8 = 0;
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6586_: u8 = 0;
    let mut v_a_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6590_: u8 = 0;
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
                v___x_6548_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_6548_) == 0 {
                    v_a_6549_ = crate::leanh::lean_ctor_get(v___x_6548_, 0);
                    v_isSharedCheck_6586_ = (!crate::leanh::lean_is_exclusive(v___x_6548_)) as u8;
                    if v_isSharedCheck_6586_ == 0 {
                        v___x_6551_ = v___x_6548_;
                        v_isShared_6552_ = v_isSharedCheck_6586_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6549_);
                        crate::leanh::lean_dec(v___x_6548_);
                        v___x_6551_ = crate::leanh::lean_box(0);
                        v_isShared_6552_ = v_isSharedCheck_6586_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_onDidChange_6545_);
                    crate::leanh::lean_dec_ref(v_handler_6544_);
                    crate::leanh::lean_dec(v_initState_6543_);
                    crate::leanh::lean_dec(v_inst_6542_);
                    crate::leanh::lean_dec_ref(v_inst_6541_);
                    crate::leanh::lean_dec_ref(v_inst_6540_);
                    crate::leanh::lean_dec_ref(v_inst_6539_);
                    crate::leanh::lean_dec(v_completeness_6538_);
                    crate::leanh::lean_dec_ref(v_method_6537_);
                    v_a_6587_ = crate::leanh::lean_ctor_get(v___x_6548_, 0);
                    v_isSharedCheck_6594_ = (!crate::leanh::lean_is_exclusive(v___x_6548_)) as u8;
                    if v_isSharedCheck_6594_ == 0 {
                        v___x_6589_ = v___x_6548_;
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6587_);
                        crate::leanh::lean_dec(v___x_6548_);
                        v___x_6589_ = crate::leanh::lean_box(0);
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6553_ = (crate::leanh::lean_unbox(v_a_6549_) as u8);
                crate::leanh::lean_dec(v_a_6549_);
                if v___x_6553_ == 0 {
                    crate::leanh::lean_dec_ref(v_onDidChange_6545_);
                    crate::leanh::lean_dec_ref(v_handler_6544_);
                    crate::leanh::lean_dec(v_initState_6543_);
                    crate::leanh::lean_dec(v_inst_6542_);
                    crate::leanh::lean_dec_ref(v_inst_6541_);
                    crate::leanh::lean_dec_ref(v_inst_6540_);
                    crate::leanh::lean_dec_ref(v_inst_6539_);
                    crate::leanh::lean_dec(v_completeness_6538_);
                    v___x_6554_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2;
                    v___x_6555_ = lean_string_append(v___x_6554_, v_method_6537_);
                    crate::leanh::lean_dec_ref(v_method_6537_);
                    v___x_6556_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__1;
                    v___x_6557_ = lean_string_append(v___x_6555_, v___x_6556_);
                    v___x_6558_ = lean_mk_io_user_error(v___x_6557_);
                    if v_isShared_6552_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6551_, 1);
                        crate::leanh::lean_ctor_set(v___x_6551_, 0, v___x_6558_);
                        v___x_6560_ = v___x_6551_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6561_, 0, v___x_6558_);
                        v___x_6560_ = v_reuseFailAlloc_6561_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6562_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once), _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3);
                    v___x_6563_ = l_Std_Mutex_new___redArg(v___x_6562_);
                    crate::leanh::lean_inc_n(v_inst_6542_, 2);
                    v___x_6564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6564_, 0, v_inst_6542_);
                    crate::leanh::lean_ctor_set(v___x_6564_, 1, v_initState_6543_);
                    crate::leanh::lean_inc_ref(v___x_6564_);
                    v___x_6565_ = lean_st_mk_ref(v___x_6564_);
                    v___x_6566_ = l_Lean_Server_statefulRequestHandlers;
                    v___x_6567_ = lean_st_ref_take(v___x_6566_);
                    v___f_6568_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7;
                    crate::leanh::lean_inc_ref(v_inst_6539_);
                    v___f_6569_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Server_registerLspRequestHandler___redArg___lam__0
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_6569_, 0, v_inst_6539_);
                    crate::leanh::lean_closure_set(v___f_6569_, 1, v_inst_6540_);
                    crate::leanh::lean_inc_ref_n(v_method_6537_, 2);
                    v___f_6570_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed as *mut core::ffi::c_void, 9, 5);
                    crate::leanh::lean_closure_set(v___f_6570_, 0, v_inst_6539_);
                    crate::leanh::lean_closure_set(v___f_6570_, 1, v_method_6537_);
                    crate::leanh::lean_closure_set(v___f_6570_, 2, v_inst_6542_);
                    crate::leanh::lean_closure_set(v___f_6570_, 3, v_handler_6544_);
                    crate::leanh::lean_closure_set(v___f_6570_, 4, v_inst_6541_);
                    v___f_6571_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 3);
                    crate::leanh::lean_closure_set(v___f_6571_, 0, v_method_6537_);
                    crate::leanh::lean_closure_set(v___f_6571_, 1, v_inst_6542_);
                    crate::leanh::lean_closure_set(v___f_6571_, 2, v_onDidChange_6545_);
                    v___f_6572_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9;
                    v___f_6573_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13;
                    v___x_6574_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__2;
                    v___f_6575_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14;
                    v___f_6576_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15;
                    crate::leanh::lean_inc_ref_n(v___x_6563_, 2);
                    crate::leanh::lean_inc_ref(v___f_6570_);
                    crate::leanh::lean_inc_n(v___x_6565_, 2);
                    v___f_6577_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed as *mut core::ffi::c_void, 11, 8);
                    crate::leanh::lean_closure_set(v___f_6577_, 0, v___x_6565_);
                    crate::leanh::lean_closure_set(v___f_6577_, 1, v___f_6570_);
                    crate::leanh::lean_closure_set(v___f_6577_, 2, v___f_6575_);
                    crate::leanh::lean_closure_set(v___f_6577_, 3, v___f_6573_);
                    crate::leanh::lean_closure_set(v___f_6577_, 4, v___x_6547_);
                    crate::leanh::lean_closure_set(v___f_6577_, 5, v___f_6568_);
                    crate::leanh::lean_closure_set(v___f_6577_, 6, v___f_6572_);
                    crate::leanh::lean_closure_set(v___f_6577_, 7, v___x_6563_);
                    crate::leanh::lean_inc_ref(v___f_6571_);
                    v___f_6578_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed as *mut core::ffi::c_void, 11, 8);
                    crate::leanh::lean_closure_set(v___f_6578_, 0, v___x_6565_);
                    crate::leanh::lean_closure_set(v___f_6578_, 1, v___f_6571_);
                    crate::leanh::lean_closure_set(v___f_6578_, 2, v___f_6576_);
                    crate::leanh::lean_closure_set(v___f_6578_, 3, v___f_6573_);
                    crate::leanh::lean_closure_set(v___f_6578_, 4, v___x_6547_);
                    crate::leanh::lean_closure_set(v___f_6578_, 5, v___f_6568_);
                    crate::leanh::lean_closure_set(v___f_6578_, 6, v___f_6572_);
                    crate::leanh::lean_closure_set(v___f_6578_, 7, v___x_6563_);
                    v___f_6579_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerLspRequestHandler___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once
                        ),
                        _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3,
                    );
                    v___x_6580_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6580_, 0, v___f_6569_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 1, v___f_6570_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 2, v___f_6577_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 3, v___f_6571_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 4, v___f_6578_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 5, v___x_6563_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 6, v___x_6564_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 7, v___x_6565_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 8, v_completeness_6538_);
                    v___x_6581_ = l_Lean_PersistentHashMap_insert___redArg(
                        v___f_6579_,
                        v___x_6574_,
                        v___x_6567_,
                        v_method_6537_,
                        v___x_6580_,
                    );
                    v___x_6582_ = lean_st_ref_set(v___x_6566_, v___x_6581_);
                    if v_isShared_6552_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6551_, 0, v___x_6582_);
                        v___x_6584_ = v___x_6551_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6585_, 0, v___x_6582_);
                        v___x_6584_ = v_reuseFailAlloc_6585_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6560_;
            }
            3 => {
                return v___x_6584_;
            }
            4 => {
                if v_isShared_6590_ == 0 {
                    v___x_6592_ = v___x_6589_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(
    mut v_method_6595_: *mut crate::leanh::LeanObject,
    mut v_completeness_6596_: *mut crate::leanh::LeanObject,
    mut v_inst_6597_: *mut crate::leanh::LeanObject,
    mut v_inst_6598_: *mut crate::leanh::LeanObject,
    mut v_inst_6599_: *mut crate::leanh::LeanObject,
    mut v_inst_6600_: *mut crate::leanh::LeanObject,
    mut v_initState_6601_: *mut crate::leanh::LeanObject,
    mut v_handler_6602_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6603_: *mut crate::leanh::LeanObject,
    mut v_a_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6605_ =
        l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(
            v_method_6595_,
            v_completeness_6596_,
            v_inst_6597_,
            v_inst_6598_,
            v_inst_6599_,
            v_inst_6600_,
            v_initState_6601_,
            v_handler_6602_,
            v_onDidChange_6603_,
        );
    return v_res_6605_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(
    mut v_method_6606_: *mut crate::leanh::LeanObject,
    mut v_completeness_6607_: *mut crate::leanh::LeanObject,
    mut v_paramType_6608_: *mut crate::leanh::LeanObject,
    mut v_inst_6609_: *mut crate::leanh::LeanObject,
    mut v_inst_6610_: *mut crate::leanh::LeanObject,
    mut v_respType_6611_: *mut crate::leanh::LeanObject,
    mut v_inst_6612_: *mut crate::leanh::LeanObject,
    mut v_stateType_6613_: *mut crate::leanh::LeanObject,
    mut v_inst_6614_: *mut crate::leanh::LeanObject,
    mut v_initState_6615_: *mut crate::leanh::LeanObject,
    mut v_handler_6616_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6619_ =
        l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(
            v_method_6606_,
            v_completeness_6607_,
            v_inst_6609_,
            v_inst_6610_,
            v_inst_6612_,
            v_inst_6614_,
            v_initState_6615_,
            v_handler_6616_,
            v_onDidChange_6617_,
        );
    return v___x_6619_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(
    mut v_method_6620_: *mut crate::leanh::LeanObject,
    mut v_completeness_6621_: *mut crate::leanh::LeanObject,
    mut v_paramType_6622_: *mut crate::leanh::LeanObject,
    mut v_inst_6623_: *mut crate::leanh::LeanObject,
    mut v_inst_6624_: *mut crate::leanh::LeanObject,
    mut v_respType_6625_: *mut crate::leanh::LeanObject,
    mut v_inst_6626_: *mut crate::leanh::LeanObject,
    mut v_stateType_6627_: *mut crate::leanh::LeanObject,
    mut v_inst_6628_: *mut crate::leanh::LeanObject,
    mut v_initState_6629_: *mut crate::leanh::LeanObject,
    mut v_handler_6630_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6631_: *mut crate::leanh::LeanObject,
    mut v_a_6632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6633_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(
        v_method_6620_,
        v_completeness_6621_,
        v_paramType_6622_,
        v_inst_6623_,
        v_inst_6624_,
        v_respType_6625_,
        v_inst_6626_,
        v_stateType_6627_,
        v_inst_6628_,
        v_initState_6629_,
        v_handler_6630_,
        v_onDidChange_6631_,
    );
    return v_res_6633_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(
    mut v_method_6634_: *mut crate::leanh::LeanObject,
    mut v_completeness_6635_: *mut crate::leanh::LeanObject,
    mut v_inst_6636_: *mut crate::leanh::LeanObject,
    mut v_inst_6637_: *mut crate::leanh::LeanObject,
    mut v_inst_6638_: *mut crate::leanh::LeanObject,
    mut v_inst_6639_: *mut crate::leanh::LeanObject,
    mut v_initState_6640_: *mut crate::leanh::LeanObject,
    mut v_handler_6641_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: u8 = 0;
    v___x_6644_ = l_Lean_Server_requestHandlers;
    v___x_6645_ = lean_st_ref_get(v___x_6644_);
    v___x_6646_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__2;
    v___f_6647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerLspRequestHandler___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once),
        _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3,
    );
    crate::leanh::lean_inc_ref(v_method_6634_);
    v___x_6648_ = l_Lean_PersistentHashMap_contains___redArg(
        v___f_6647_,
        v___x_6646_,
        v___x_6645_,
        v_method_6634_,
    );
    if v___x_6648_ == 0 {
        let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6649_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_6634_, v_completeness_6635_, v_inst_6636_, v_inst_6637_, v_inst_6638_, v_inst_6639_, v_initState_6640_, v_handler_6641_, v_onDidChange_6642_);
        return v___x_6649_;
    } else {
        let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_onDidChange_6642_);
        crate::leanh::lean_dec_ref(v_handler_6641_);
        crate::leanh::lean_dec(v_initState_6640_);
        crate::leanh::lean_dec(v_inst_6639_);
        crate::leanh::lean_dec_ref(v_inst_6638_);
        crate::leanh::lean_dec_ref(v_inst_6637_);
        crate::leanh::lean_dec_ref(v_inst_6636_);
        crate::leanh::lean_dec(v_completeness_6635_);
        v___x_6650_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2;
        v___x_6651_ = lean_string_append(v___x_6650_, v_method_6634_);
        crate::leanh::lean_dec_ref(v_method_6634_);
        v___x_6652_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__4;
        v___x_6653_ = lean_string_append(v___x_6651_, v___x_6652_);
        v___x_6654_ = lean_mk_io_user_error(v___x_6653_);
        v___x_6655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6655_, 0, v___x_6654_);
        return v___x_6655_;
    }
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(
    mut v_method_6656_: *mut crate::leanh::LeanObject,
    mut v_completeness_6657_: *mut crate::leanh::LeanObject,
    mut v_inst_6658_: *mut crate::leanh::LeanObject,
    mut v_inst_6659_: *mut crate::leanh::LeanObject,
    mut v_inst_6660_: *mut crate::leanh::LeanObject,
    mut v_inst_6661_: *mut crate::leanh::LeanObject,
    mut v_initState_6662_: *mut crate::leanh::LeanObject,
    mut v_handler_6663_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6664_: *mut crate::leanh::LeanObject,
    mut v_a_6665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6666_ =
        l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(
            v_method_6656_,
            v_completeness_6657_,
            v_inst_6658_,
            v_inst_6659_,
            v_inst_6660_,
            v_inst_6661_,
            v_initState_6662_,
            v_handler_6663_,
            v_onDidChange_6664_,
        );
    return v_res_6666_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(
    mut v_method_6667_: *mut crate::leanh::LeanObject,
    mut v_completeness_6668_: *mut crate::leanh::LeanObject,
    mut v_paramType_6669_: *mut crate::leanh::LeanObject,
    mut v_inst_6670_: *mut crate::leanh::LeanObject,
    mut v_inst_6671_: *mut crate::leanh::LeanObject,
    mut v_respType_6672_: *mut crate::leanh::LeanObject,
    mut v_inst_6673_: *mut crate::leanh::LeanObject,
    mut v_stateType_6674_: *mut crate::leanh::LeanObject,
    mut v_inst_6675_: *mut crate::leanh::LeanObject,
    mut v_initState_6676_: *mut crate::leanh::LeanObject,
    mut v_handler_6677_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6680_ =
        l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(
            v_method_6667_,
            v_completeness_6668_,
            v_inst_6670_,
            v_inst_6671_,
            v_inst_6673_,
            v_inst_6675_,
            v_initState_6676_,
            v_handler_6677_,
            v_onDidChange_6678_,
        );
    return v___x_6680_;
}
pub unsafe fn l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(
    mut v_method_6681_: *mut crate::leanh::LeanObject,
    mut v_completeness_6682_: *mut crate::leanh::LeanObject,
    mut v_paramType_6683_: *mut crate::leanh::LeanObject,
    mut v_inst_6684_: *mut crate::leanh::LeanObject,
    mut v_inst_6685_: *mut crate::leanh::LeanObject,
    mut v_respType_6686_: *mut crate::leanh::LeanObject,
    mut v_inst_6687_: *mut crate::leanh::LeanObject,
    mut v_stateType_6688_: *mut crate::leanh::LeanObject,
    mut v_inst_6689_: *mut crate::leanh::LeanObject,
    mut v_initState_6690_: *mut crate::leanh::LeanObject,
    mut v_handler_6691_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6692_: *mut crate::leanh::LeanObject,
    mut v_a_6693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6694_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(
        v_method_6681_,
        v_completeness_6682_,
        v_paramType_6683_,
        v_inst_6684_,
        v_inst_6685_,
        v_respType_6686_,
        v_inst_6687_,
        v_stateType_6688_,
        v_inst_6689_,
        v_initState_6690_,
        v_handler_6691_,
        v_onDidChange_6692_,
    );
    return v_res_6694_;
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(
    mut v_handler_6695_: *mut crate::leanh::LeanObject,
    mut v_p_6696_: *mut crate::leanh::LeanObject,
    mut v_s_6697_: *mut crate::leanh::LeanObject,
    mut v___y_6698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6704_: u8 = 0;
    let mut v_fst_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6709_: u8 = 0;
    let mut v___x_6710_: u8 = 0;
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6718_: u8 = 0;
    let mut v_isSharedCheck_6719_: u8 = 0;
    let mut v_a_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_6698_);
                v___x_6700_ = crate::leanh::lean_apply_4(
                    v_handler_6695_,
                    v_p_6696_,
                    v_s_6697_,
                    v___y_6698_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6700_) == 0 {
                    v_a_6701_ = crate::leanh::lean_ctor_get(v___x_6700_, 0);
                    v_isSharedCheck_6719_ = (!crate::leanh::lean_is_exclusive(v___x_6700_)) as u8;
                    if v_isSharedCheck_6719_ == 0 {
                        v___x_6703_ = v___x_6700_;
                        v_isShared_6704_ = v_isSharedCheck_6719_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6701_);
                        crate::leanh::lean_dec(v___x_6700_);
                        v___x_6703_ = crate::leanh::lean_box(0);
                        v_isShared_6704_ = v_isSharedCheck_6719_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6720_ = crate::leanh::lean_ctor_get(v___x_6700_, 0);
                    v_isSharedCheck_6727_ = (!crate::leanh::lean_is_exclusive(v___x_6700_)) as u8;
                    if v_isSharedCheck_6727_ == 0 {
                        v___x_6722_ = v___x_6700_;
                        v_isShared_6723_ = v_isSharedCheck_6727_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6720_);
                        crate::leanh::lean_dec(v___x_6700_);
                        v___x_6722_ = crate::leanh::lean_box(0);
                        v_isShared_6723_ = v_isSharedCheck_6727_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6705_ = crate::leanh::lean_ctor_get(v_a_6701_, 0);
                v_snd_6706_ = crate::leanh::lean_ctor_get(v_a_6701_, 1);
                v_isSharedCheck_6718_ = (!crate::leanh::lean_is_exclusive(v_a_6701_)) as u8;
                if v_isSharedCheck_6718_ == 0 {
                    v___x_6708_ = v_a_6701_;
                    v_isShared_6709_ = v_isSharedCheck_6718_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6706_);
                    crate::leanh::lean_inc(v_fst_6705_);
                    crate::leanh::lean_dec(v_a_6701_);
                    v___x_6708_ = crate::leanh::lean_box(0);
                    v_isShared_6709_ = v_isSharedCheck_6718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6710_ = 1;
                v___x_6711_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6711_, 0, v_fst_6705_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6711_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6710_,
                );
                if v_isShared_6709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6708_, 0, v___x_6711_);
                    v___x_6713_ = v___x_6708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6717_, 0, v___x_6711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6717_, 1, v_snd_6706_);
                    v___x_6713_ = v_reuseFailAlloc_6717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6703_, 0, v___x_6713_);
                    v___x_6715_ = v___x_6703_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 0, v___x_6713_);
                    v___x_6715_ = v_reuseFailAlloc_6716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6715_;
            }
            5 => {
                if v_isShared_6723_ == 0 {
                    v___x_6725_ = v___x_6722_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6726_, 0, v_a_6720_);
                    v___x_6725_ = v_reuseFailAlloc_6726_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(
    mut v_handler_6728_: *mut crate::leanh::LeanObject,
    mut v_p_6729_: *mut crate::leanh::LeanObject,
    mut v_s_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6733_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(
        v_handler_6728_,
        v_p_6729_,
        v_s_6730_,
        v___y_6731_,
    );
    crate::leanh::lean_dec_ref(v___y_6731_);
    return v_res_6733_;
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(
    mut v_method_6734_: *mut crate::leanh::LeanObject,
    mut v_inst_6735_: *mut crate::leanh::LeanObject,
    mut v_inst_6736_: *mut crate::leanh::LeanObject,
    mut v_inst_6737_: *mut crate::leanh::LeanObject,
    mut v_inst_6738_: *mut crate::leanh::LeanObject,
    mut v_initState_6739_: *mut crate::leanh::LeanObject,
    mut v_handler_6740_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_handler_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_handler_6743_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v_handler_6743_, 0, v_handler_6740_);
    v___x_6744_ = crate::leanh::lean_box(0);
    v___x_6745_ =
        l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(
            v_method_6734_,
            v___x_6744_,
            v_inst_6735_,
            v_inst_6736_,
            v_inst_6737_,
            v_inst_6738_,
            v_initState_6739_,
            v_handler_6743_,
            v_onDidChange_6741_,
        );
    return v___x_6745_;
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(
    mut v_method_6746_: *mut crate::leanh::LeanObject,
    mut v_inst_6747_: *mut crate::leanh::LeanObject,
    mut v_inst_6748_: *mut crate::leanh::LeanObject,
    mut v_inst_6749_: *mut crate::leanh::LeanObject,
    mut v_inst_6750_: *mut crate::leanh::LeanObject,
    mut v_initState_6751_: *mut crate::leanh::LeanObject,
    mut v_handler_6752_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6753_: *mut crate::leanh::LeanObject,
    mut v_a_6754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6755_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(
        v_method_6746_,
        v_inst_6747_,
        v_inst_6748_,
        v_inst_6749_,
        v_inst_6750_,
        v_initState_6751_,
        v_handler_6752_,
        v_onDidChange_6753_,
    );
    return v_res_6755_;
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler(
    mut v_method_6756_: *mut crate::leanh::LeanObject,
    mut v_paramType_6757_: *mut crate::leanh::LeanObject,
    mut v_inst_6758_: *mut crate::leanh::LeanObject,
    mut v_inst_6759_: *mut crate::leanh::LeanObject,
    mut v_respType_6760_: *mut crate::leanh::LeanObject,
    mut v_inst_6761_: *mut crate::leanh::LeanObject,
    mut v_stateType_6762_: *mut crate::leanh::LeanObject,
    mut v_inst_6763_: *mut crate::leanh::LeanObject,
    mut v_initState_6764_: *mut crate::leanh::LeanObject,
    mut v_handler_6765_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6768_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(
        v_method_6756_,
        v_inst_6758_,
        v_inst_6759_,
        v_inst_6761_,
        v_inst_6763_,
        v_initState_6764_,
        v_handler_6765_,
        v_onDidChange_6766_,
    );
    return v___x_6768_;
}
pub unsafe fn l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(
    mut v_method_6769_: *mut crate::leanh::LeanObject,
    mut v_paramType_6770_: *mut crate::leanh::LeanObject,
    mut v_inst_6771_: *mut crate::leanh::LeanObject,
    mut v_inst_6772_: *mut crate::leanh::LeanObject,
    mut v_respType_6773_: *mut crate::leanh::LeanObject,
    mut v_inst_6774_: *mut crate::leanh::LeanObject,
    mut v_stateType_6775_: *mut crate::leanh::LeanObject,
    mut v_inst_6776_: *mut crate::leanh::LeanObject,
    mut v_initState_6777_: *mut crate::leanh::LeanObject,
    mut v_handler_6778_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6779_: *mut crate::leanh::LeanObject,
    mut v_a_6780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6781_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(
        v_method_6769_,
        v_paramType_6770_,
        v_inst_6771_,
        v_inst_6772_,
        v_respType_6773_,
        v_inst_6774_,
        v_stateType_6775_,
        v_inst_6776_,
        v_initState_6777_,
        v_handler_6778_,
        v_onDidChange_6779_,
    );
    return v_res_6781_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(
    mut v_method_6782_: *mut crate::leanh::LeanObject,
    mut v_refreshMethod_6783_: *mut crate::leanh::LeanObject,
    mut v_refreshIntervalMs_6784_: *mut crate::leanh::LeanObject,
    mut v_inst_6785_: *mut crate::leanh::LeanObject,
    mut v_inst_6786_: *mut crate::leanh::LeanObject,
    mut v_inst_6787_: *mut crate::leanh::LeanObject,
    mut v_inst_6788_: *mut crate::leanh::LeanObject,
    mut v_initState_6789_: *mut crate::leanh::LeanObject,
    mut v_handler_6790_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6793_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6793_, 0, v_refreshMethod_6783_);
    crate::leanh::lean_ctor_set(v___x_6793_, 1, v_refreshIntervalMs_6784_);
    v___x_6794_ =
        l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(
            v_method_6782_,
            v___x_6793_,
            v_inst_6785_,
            v_inst_6786_,
            v_inst_6787_,
            v_inst_6788_,
            v_initState_6789_,
            v_handler_6790_,
            v_onDidChange_6791_,
        );
    return v___x_6794_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(
    mut v_method_6795_: *mut crate::leanh::LeanObject,
    mut v_refreshMethod_6796_: *mut crate::leanh::LeanObject,
    mut v_refreshIntervalMs_6797_: *mut crate::leanh::LeanObject,
    mut v_inst_6798_: *mut crate::leanh::LeanObject,
    mut v_inst_6799_: *mut crate::leanh::LeanObject,
    mut v_inst_6800_: *mut crate::leanh::LeanObject,
    mut v_inst_6801_: *mut crate::leanh::LeanObject,
    mut v_initState_6802_: *mut crate::leanh::LeanObject,
    mut v_handler_6803_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6804_: *mut crate::leanh::LeanObject,
    mut v_a_6805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6806_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(
        v_method_6795_,
        v_refreshMethod_6796_,
        v_refreshIntervalMs_6797_,
        v_inst_6798_,
        v_inst_6799_,
        v_inst_6800_,
        v_inst_6801_,
        v_initState_6802_,
        v_handler_6803_,
        v_onDidChange_6804_,
    );
    return v_res_6806_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler(
    mut v_method_6807_: *mut crate::leanh::LeanObject,
    mut v_refreshMethod_6808_: *mut crate::leanh::LeanObject,
    mut v_refreshIntervalMs_6809_: *mut crate::leanh::LeanObject,
    mut v_paramType_6810_: *mut crate::leanh::LeanObject,
    mut v_inst_6811_: *mut crate::leanh::LeanObject,
    mut v_inst_6812_: *mut crate::leanh::LeanObject,
    mut v_respType_6813_: *mut crate::leanh::LeanObject,
    mut v_inst_6814_: *mut crate::leanh::LeanObject,
    mut v_stateType_6815_: *mut crate::leanh::LeanObject,
    mut v_inst_6816_: *mut crate::leanh::LeanObject,
    mut v_initState_6817_: *mut crate::leanh::LeanObject,
    mut v_handler_6818_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6821_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(
        v_method_6807_,
        v_refreshMethod_6808_,
        v_refreshIntervalMs_6809_,
        v_inst_6811_,
        v_inst_6812_,
        v_inst_6814_,
        v_inst_6816_,
        v_initState_6817_,
        v_handler_6818_,
        v_onDidChange_6819_,
    );
    return v___x_6821_;
}
pub unsafe fn l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(
    mut v_method_6822_: *mut crate::leanh::LeanObject,
    mut v_refreshMethod_6823_: *mut crate::leanh::LeanObject,
    mut v_refreshIntervalMs_6824_: *mut crate::leanh::LeanObject,
    mut v_paramType_6825_: *mut crate::leanh::LeanObject,
    mut v_inst_6826_: *mut crate::leanh::LeanObject,
    mut v_inst_6827_: *mut crate::leanh::LeanObject,
    mut v_respType_6828_: *mut crate::leanh::LeanObject,
    mut v_inst_6829_: *mut crate::leanh::LeanObject,
    mut v_stateType_6830_: *mut crate::leanh::LeanObject,
    mut v_inst_6831_: *mut crate::leanh::LeanObject,
    mut v_initState_6832_: *mut crate::leanh::LeanObject,
    mut v_handler_6833_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_6834_: *mut crate::leanh::LeanObject,
    mut v_a_6835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6836_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(
        v_method_6822_,
        v_refreshMethod_6823_,
        v_refreshIntervalMs_6824_,
        v_paramType_6825_,
        v_inst_6826_,
        v_inst_6827_,
        v_respType_6828_,
        v_inst_6829_,
        v_stateType_6830_,
        v_inst_6831_,
        v_initState_6832_,
        v_handler_6833_,
        v_onDidChange_6834_,
    );
    return v_res_6836_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(
    mut v_keys_6837_: *mut crate::leanh::LeanObject,
    mut v_i_6838_: *mut crate::leanh::LeanObject,
    mut v_k_6839_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: u8 = 0;
    let mut v_k_x27_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: u8 = 0;
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6840_ = lean_array_get_size(v_keys_6837_);
                v___x_6841_ = lean_nat_dec_lt(v_i_6838_, v___x_6840_);
                if v___x_6841_ == 0 {
                    crate::leanh::lean_dec(v_i_6838_);
                    return v___x_6841_;
                } else {
                    v_k_x27_6842_ = lean_array_fget_borrowed(v_keys_6837_, v_i_6838_);
                    v___x_6843_ = lean_string_dec_eq(v_k_6839_, v_k_x27_6842_);
                    if v___x_6843_ == 0 {
                        v___x_6844_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6845_ = lean_nat_add(v_i_6838_, v___x_6844_);
                        crate::leanh::lean_dec(v_i_6838_);
                        v_i_6838_ = v___x_6845_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_6838_);
                        return v___x_6843_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_6847_: *mut crate::leanh::LeanObject,
    mut v_i_6848_: *mut crate::leanh::LeanObject,
    mut v_k_6849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6850_: u8 = 0;
    let mut v_r_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6850_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_6847_, v_i_6848_, v_k_6849_);
    crate::leanh::lean_dec_ref(v_k_6849_);
    crate::leanh::lean_dec_ref(v_keys_6847_);
    v_r_6851_ = crate::leanh::lean_box((v_res_6850_) as usize);
    return v_r_6851_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(
    mut v_x_6852_: *mut crate::leanh::LeanObject,
    mut v_x_6853_: usize,
    mut v_x_6854_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: usize = 0;
    let mut v___x_6858_: usize = 0;
    let mut v___x_6859_: usize = 0;
    let mut v_j_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: u8 = 0;
    let mut v_node_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: usize = 0;
    let mut v___x_6867_: u8 = 0;
    let mut v_ks_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6852_) == 0 {
                    v_es_6855_ = crate::leanh::lean_ctor_get(v_x_6852_, 0);
                    v___x_6856_ = crate::leanh::lean_box(2);
                    v___x_6857_ = 5usize;
                    v___x_6858_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1);
                    v___x_6859_ = lean_usize_land(v_x_6853_, v___x_6858_);
                    v_j_6860_ = lean_usize_to_nat(v___x_6859_);
                    v___x_6861_ = lean_array_get_borrowed(v___x_6856_, v_es_6855_, v_j_6860_);
                    crate::leanh::lean_dec(v_j_6860_);
                    match crate::leanh::lean_obj_tag(v___x_6861_) {
                        0 => {
                            v_key_6862_ = crate::leanh::lean_ctor_get(v___x_6861_, 0);
                            v___x_6863_ = lean_string_dec_eq(v_x_6854_, v_key_6862_);
                            return v___x_6863_;
                        }
                        1 => {
                            v_node_6864_ = crate::leanh::lean_ctor_get(v___x_6861_, 0);
                            v___x_6865_ = lean_usize_shift_right(v_x_6853_, v___x_6857_);
                            v_x_6852_ = v_node_6864_;
                            v_x_6853_ = v___x_6865_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6867_ = 0;
                            return v___x_6867_;
                        }
                    }
                } else {
                    v_ks_6868_ = crate::leanh::lean_ctor_get(v_x_6852_, 0);
                    v___x_6869_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6870_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_6868_, v___x_6869_, v_x_6854_);
                    return v___x_6870_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(
    mut v_x_6871_: *mut crate::leanh::LeanObject,
    mut v_x_6872_: *mut crate::leanh::LeanObject,
    mut v_x_6873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_224__boxed_6874_: usize = 0;
    let mut v_res_6875_: u8 = 0;
    let mut v_r_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_224__boxed_6874_ = crate::leanh::lean_unbox_usize(v_x_6872_);
    crate::leanh::lean_dec(v_x_6872_);
    v_res_6875_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_6871_, v_x_224__boxed_6874_, v_x_6873_);
    crate::leanh::lean_dec_ref(v_x_6873_);
    crate::leanh::lean_dec_ref(v_x_6871_);
    v_r_6876_ = crate::leanh::lean_box((v_res_6875_) as usize);
    return v_r_6876_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(
    mut v_x_6877_: *mut crate::leanh::LeanObject,
    mut v_x_6878_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6879_: u64 = 0;
    let mut v___x_6880_: usize = 0;
    let mut v___x_6881_: u8 = 0;
    v___x_6879_ = lean_string_hash(v_x_6878_);
    v___x_6880_ = lean_uint64_to_usize(v___x_6879_);
    v___x_6881_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_6877_, v___x_6880_, v_x_6878_);
    return v___x_6881_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(
    mut v_x_6882_: *mut crate::leanh::LeanObject,
    mut v_x_6883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6884_: u8 = 0;
    let mut v_r_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6884_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_6882_, v_x_6883_);
    crate::leanh::lean_dec_ref(v_x_6883_);
    crate::leanh::lean_dec_ref(v_x_6882_);
    v_r_6885_ = crate::leanh::lean_box((v_res_6884_) as usize);
    return v_r_6885_;
}
pub unsafe fn l_Lean_Server_isStatefulLspRequestMethod(
    mut v_method_6886_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: u8 = 0;
    v___x_6888_ = l_Lean_Server_statefulRequestHandlers;
    v___x_6889_ = lean_st_ref_get(v___x_6888_);
    v___x_6890_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_6889_, v_method_6886_);
    crate::leanh::lean_dec(v___x_6889_);
    return v___x_6890_;
}
pub unsafe fn l_Lean_Server_isStatefulLspRequestMethod___boxed(
    mut v_method_6891_: *mut crate::leanh::LeanObject,
    mut v_a_6892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6893_: u8 = 0;
    let mut v_r_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6893_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_6891_);
    crate::leanh::lean_dec_ref(v_method_6891_);
    v_r_6894_ = crate::leanh::lean_box((v_res_6893_) as usize);
    return v_r_6894_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(
    mut v_00_u03b2_6895_: *mut crate::leanh::LeanObject,
    mut v_x_6896_: *mut crate::leanh::LeanObject,
    mut v_x_6897_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6898_: u8 = 0;
    v___x_6898_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_6896_, v_x_6897_);
    return v___x_6898_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(
    mut v_00_u03b2_6899_: *mut crate::leanh::LeanObject,
    mut v_x_6900_: *mut crate::leanh::LeanObject,
    mut v_x_6901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6902_: u8 = 0;
    let mut v_r_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6902_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(
            v_00_u03b2_6899_,
            v_x_6900_,
            v_x_6901_,
        );
    crate::leanh::lean_dec_ref(v_x_6901_);
    crate::leanh::lean_dec_ref(v_x_6900_);
    v_r_6903_ = crate::leanh::lean_box((v_res_6902_) as usize);
    return v_r_6903_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(
    mut v_00_u03b2_6904_: *mut crate::leanh::LeanObject,
    mut v_x_6905_: *mut crate::leanh::LeanObject,
    mut v_x_6906_: usize,
    mut v_x_6907_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6908_: u8 = 0;
    v___x_6908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_6905_, v_x_6906_, v_x_6907_);
    return v___x_6908_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(
    mut v_00_u03b2_6909_: *mut crate::leanh::LeanObject,
    mut v_x_6910_: *mut crate::leanh::LeanObject,
    mut v_x_6911_: *mut crate::leanh::LeanObject,
    mut v_x_6912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_296__boxed_6913_: usize = 0;
    let mut v_res_6914_: u8 = 0;
    let mut v_r_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_296__boxed_6913_ = crate::leanh::lean_unbox_usize(v_x_6911_);
    crate::leanh::lean_dec(v_x_6911_);
    v_res_6914_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_6909_, v_x_6910_, v_x_296__boxed_6913_, v_x_6912_);
    crate::leanh::lean_dec_ref(v_x_6912_);
    crate::leanh::lean_dec_ref(v_x_6910_);
    v_r_6915_ = crate::leanh::lean_box((v_res_6914_) as usize);
    return v_r_6915_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6916_: *mut crate::leanh::LeanObject,
    mut v_keys_6917_: *mut crate::leanh::LeanObject,
    mut v_vals_6918_: *mut crate::leanh::LeanObject,
    mut v_heq_6919_: *mut crate::leanh::LeanObject,
    mut v_i_6920_: *mut crate::leanh::LeanObject,
    mut v_k_6921_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6922_: u8 = 0;
    v___x_6922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_6917_, v_i_6920_, v_k_6921_);
    return v___x_6922_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_6923_: *mut crate::leanh::LeanObject,
    mut v_keys_6924_: *mut crate::leanh::LeanObject,
    mut v_vals_6925_: *mut crate::leanh::LeanObject,
    mut v_heq_6926_: *mut crate::leanh::LeanObject,
    mut v_i_6927_: *mut crate::leanh::LeanObject,
    mut v_k_6928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6929_: u8 = 0;
    let mut v_r_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_6923_, v_keys_6924_, v_vals_6925_, v_heq_6926_, v_i_6927_, v_k_6928_);
    crate::leanh::lean_dec_ref(v_k_6928_);
    crate::leanh::lean_dec_ref(v_vals_6925_);
    crate::leanh::lean_dec_ref(v_keys_6924_);
    v_r_6930_ = crate::leanh::lean_box((v_res_6929_) as usize);
    return v_r_6930_;
}
pub unsafe fn l_Lean_Server_lookupStatefulLspRequestHandler(
    mut v_method_6931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6933_ = l_Lean_Server_statefulRequestHandlers;
    v___x_6934_ = lean_st_ref_get(v___x_6933_);
    v___x_6935_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_6934_, v_method_6931_);
    crate::leanh::lean_dec(v___x_6934_);
    return v___x_6935_;
}
pub unsafe fn l_Lean_Server_lookupStatefulLspRequestHandler___boxed(
    mut v_method_6936_: *mut crate::leanh::LeanObject,
    mut v_a_6937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6938_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_6936_);
    crate::leanh::lean_dec_ref(v_method_6936_);
    return v_res_6938_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(
    mut v_as_6939_: *mut crate::leanh::LeanObject,
    mut v_i_6940_: usize,
    mut v_stop_6941_: usize,
    mut v_b_6942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: usize = 0;
    let mut v___x_6946_: usize = 0;
    let mut v___x_6948_: u8 = 0;
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_completeness_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v_refreshMethod_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_refreshIntervalMs_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6960_: u8 = 0;
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut v_isSharedCheck_6969_: u8 = 0;
    let mut v_unused_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6948_ = lean_usize_dec_eq(v_i_6940_, v_stop_6941_);
                if v___x_6948_ == 0 {
                    v___x_6949_ = lean_array_uget(v_as_6939_, v_i_6940_);
                    v_snd_6950_ = crate::leanh::lean_ctor_get(v___x_6949_, 1);
                    v_completeness_6951_ = crate::leanh::lean_ctor_get(v_snd_6950_, 8);
                    crate::leanh::lean_inc(v_completeness_6951_);
                    if crate::leanh::lean_obj_tag(v_completeness_6951_) == 1 {
                        v_fst_6952_ = crate::leanh::lean_ctor_get(v___x_6949_, 0);
                        v_isSharedCheck_6969_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6949_)) as u8;
                        if v_isSharedCheck_6969_ == 0 {
                            v_unused_6970_ = crate::leanh::lean_ctor_get(v___x_6949_, 1);
                            crate::leanh::lean_dec(v_unused_6970_);
                            v___x_6954_ = v___x_6949_;
                            v_isShared_6955_ = v_isSharedCheck_6969_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_6952_);
                            crate::leanh::lean_dec(v___x_6949_);
                            v___x_6954_ = crate::leanh::lean_box(0);
                            v_isShared_6955_ = v_isSharedCheck_6969_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_completeness_6951_);
                        crate::leanh::lean_dec(v___x_6949_);
                        v___y_6944_ = v_b_6942_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6942_;
                }
            }
            1 => {
                v___x_6945_ = 1usize;
                v___x_6946_ = lean_usize_add(v_i_6940_, v___x_6945_);
                v_i_6940_ = v___x_6946_;
                v_b_6942_ = v___y_6944_;
                state = 0;
                continue;
            }
            2 => {
                v_refreshMethod_6956_ = crate::leanh::lean_ctor_get(v_completeness_6951_, 0);
                v_refreshIntervalMs_6957_ = crate::leanh::lean_ctor_get(v_completeness_6951_, 1);
                v_isSharedCheck_6968_ =
                    (!crate::leanh::lean_is_exclusive(v_completeness_6951_)) as u8;
                if v_isSharedCheck_6968_ == 0 {
                    v___x_6959_ = v_completeness_6951_;
                    v_isShared_6960_ = v_isSharedCheck_6968_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_refreshIntervalMs_6957_);
                    crate::leanh::lean_inc(v_refreshMethod_6956_);
                    crate::leanh::lean_dec(v_completeness_6951_);
                    v___x_6959_ = crate::leanh::lean_box(0);
                    v_isShared_6960_ = v_isSharedCheck_6968_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6954_, 1, v_refreshIntervalMs_6957_);
                    crate::leanh::lean_ctor_set(v___x_6954_, 0, v_refreshMethod_6956_);
                    v___x_6962_ = v___x_6954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6967_, 0, v_refreshMethod_6956_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6967_,
                        1,
                        v_refreshIntervalMs_6957_,
                    );
                    v___x_6962_ = v_reuseFailAlloc_6967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6960_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6959_, 0);
                    crate::leanh::lean_ctor_set(v___x_6959_, 1, v___x_6962_);
                    crate::leanh::lean_ctor_set(v___x_6959_, 0, v_fst_6952_);
                    v___x_6964_ = v___x_6959_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6966_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 0, v_fst_6952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 1, v___x_6962_);
                    v___x_6964_ = v_reuseFailAlloc_6966_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6965_ = lean_array_push(v_b_6942_, v___x_6964_);
                v___y_6944_ = v___x_6965_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(
    mut v_as_6971_: *mut crate::leanh::LeanObject,
    mut v_i_6972_: *mut crate::leanh::LeanObject,
    mut v_stop_6973_: *mut crate::leanh::LeanObject,
    mut v_b_6974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6975_: usize = 0;
    let mut v_stop_boxed_6976_: usize = 0;
    let mut v_res_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6975_ = crate::leanh::lean_unbox_usize(v_i_6972_);
    crate::leanh::lean_dec(v_i_6972_);
    v_stop_boxed_6976_ = crate::leanh::lean_unbox_usize(v_stop_6973_);
    crate::leanh::lean_dec(v_stop_6973_);
    v_res_6977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_6971_, v_i_boxed_6975_, v_stop_boxed_6976_, v_b_6974_);
    crate::leanh::lean_dec_ref(v_as_6971_);
    return v_res_6977_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(
    mut v_as_6980_: *mut crate::leanh::LeanObject,
    mut v_start_6981_: *mut crate::leanh::LeanObject,
    mut v_stop_6982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: u8 = 0;
    v___x_6983_ =
        l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0;
    v___x_6984_ = lean_nat_dec_lt(v_start_6981_, v_stop_6982_);
    if v___x_6984_ == 0 {
        return v___x_6983_;
    } else {
        let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6986_: u8 = 0;
        v___x_6985_ = lean_array_get_size(v_as_6980_);
        v___x_6986_ = lean_nat_dec_le(v_stop_6982_, v___x_6985_);
        if v___x_6986_ == 0 {
            let mut v___x_6987_: u8 = 0;
            v___x_6987_ = lean_nat_dec_lt(v_start_6981_, v___x_6985_);
            if v___x_6987_ == 0 {
                return v___x_6983_;
            } else {
                let mut v___x_6988_: usize = 0;
                let mut v___x_6989_: usize = 0;
                let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6988_ = lean_usize_of_nat(v_start_6981_);
                v___x_6989_ = lean_usize_of_nat(v___x_6985_);
                v___x_6990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_6980_, v___x_6988_, v___x_6989_, v___x_6983_);
                return v___x_6990_;
            }
        } else {
            let mut v___x_6991_: usize = 0;
            let mut v___x_6992_: usize = 0;
            let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6991_ = lean_usize_of_nat(v_start_6981_);
            v___x_6992_ = lean_usize_of_nat(v_stop_6982_);
            v___x_6993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_6980_, v___x_6991_, v___x_6992_, v___x_6983_);
            return v___x_6993_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(
    mut v_as_6994_: *mut crate::leanh::LeanObject,
    mut v_start_6995_: *mut crate::leanh::LeanObject,
    mut v_stop_6996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6997_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(
        v_as_6994_,
        v_start_6995_,
        v_stop_6996_,
    );
    crate::leanh::lean_dec(v_stop_6996_);
    crate::leanh::lean_dec(v_start_6995_);
    crate::leanh::lean_dec_ref(v_as_6994_);
    return v_res_6997_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_f_6998_: *mut crate::leanh::LeanObject,
    mut v_keys_6999_: *mut crate::leanh::LeanObject,
    mut v_vals_7000_: *mut crate::leanh::LeanObject,
    mut v_i_7001_: *mut crate::leanh::LeanObject,
    mut v_acc_7002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: u8 = 0;
    let mut v_k_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7003_ = lean_array_get_size(v_keys_6999_);
                v___x_7004_ = lean_nat_dec_lt(v_i_7001_, v___x_7003_);
                if v___x_7004_ == 0 {
                    crate::leanh::lean_dec(v_i_7001_);
                    crate::leanh::lean_dec(v_f_6998_);
                    return v_acc_7002_;
                } else {
                    v_k_7005_ = lean_array_fget_borrowed(v_keys_6999_, v_i_7001_);
                    v_v_7006_ = lean_array_fget_borrowed(v_vals_7000_, v_i_7001_);
                    crate::leanh::lean_inc(v_f_6998_);
                    crate::leanh::lean_inc(v_v_7006_);
                    crate::leanh::lean_inc(v_k_7005_);
                    v___x_7007_ =
                        crate::leanh::lean_apply_3(v_f_6998_, v_acc_7002_, v_k_7005_, v_v_7006_);
                    v___x_7008_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7009_ = lean_nat_add(v_i_7001_, v___x_7008_);
                    crate::leanh::lean_dec(v_i_7001_);
                    v_i_7001_ = v___x_7009_;
                    v_acc_7002_ = v___x_7007_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_f_7011_: *mut crate::leanh::LeanObject,
    mut v_keys_7012_: *mut crate::leanh::LeanObject,
    mut v_vals_7013_: *mut crate::leanh::LeanObject,
    mut v_i_7014_: *mut crate::leanh::LeanObject,
    mut v_acc_7015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_7011_, v_keys_7012_, v_vals_7013_, v_i_7014_, v_acc_7015_);
    crate::leanh::lean_dec_ref(v_vals_7013_);
    crate::leanh::lean_dec_ref(v_keys_7012_);
    return v_res_7016_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_7017_: *mut crate::leanh::LeanObject,
    mut v_x_7018_: *mut crate::leanh::LeanObject,
    mut v_x_7019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7018_) == 0 {
        let mut v_es_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7023_: u8 = 0;
        v_es_7020_ = crate::leanh::lean_ctor_get(v_x_7018_, 0);
        v___x_7021_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_7022_ = lean_array_get_size(v_es_7020_);
        v___x_7023_ = lean_nat_dec_lt(v___x_7021_, v___x_7022_);
        if v___x_7023_ == 0 {
            crate::leanh::lean_dec(v_f_7017_);
            return v_x_7019_;
        } else {
            let mut v___x_7024_: u8 = 0;
            v___x_7024_ = lean_nat_dec_le(v___x_7022_, v___x_7022_);
            if v___x_7024_ == 0 {
                if v___x_7023_ == 0 {
                    crate::leanh::lean_dec(v_f_7017_);
                    return v_x_7019_;
                } else {
                    let mut v___x_7025_: usize = 0;
                    let mut v___x_7026_: usize = 0;
                    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_7025_ = 0usize;
                    v___x_7026_ = lean_usize_of_nat(v___x_7022_);
                    v___x_7027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_7017_, v_es_7020_, v___x_7025_, v___x_7026_, v_x_7019_);
                    return v___x_7027_;
                }
            } else {
                let mut v___x_7028_: usize = 0;
                let mut v___x_7029_: usize = 0;
                let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_7028_ = 0usize;
                v___x_7029_ = lean_usize_of_nat(v___x_7022_);
                v___x_7030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_7017_, v_es_7020_, v___x_7028_, v___x_7029_, v_x_7019_);
                return v___x_7030_;
            }
        }
    } else {
        let mut v_ks_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_7031_ = crate::leanh::lean_ctor_get(v_x_7018_, 0);
        v_vs_7032_ = crate::leanh::lean_ctor_get(v_x_7018_, 1);
        v___x_7033_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_7034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_7017_, v_ks_7031_, v_vs_7032_, v___x_7033_, v_x_7019_);
        return v___x_7034_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_f_7035_: *mut crate::leanh::LeanObject,
    mut v_as_7036_: *mut crate::leanh::LeanObject,
    mut v_i_7037_: usize,
    mut v_stop_7038_: usize,
    mut v_b_7039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: usize = 0;
    let mut v___x_7043_: usize = 0;
    let mut v___x_7045_: u8 = 0;
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7045_ = lean_usize_dec_eq(v_i_7037_, v_stop_7038_);
                if v___x_7045_ == 0 {
                    v___x_7046_ = lean_array_uget_borrowed(v_as_7036_, v_i_7037_);
                    match crate::leanh::lean_obj_tag(v___x_7046_) {
                        0 => {
                            v_key_7047_ = crate::leanh::lean_ctor_get(v___x_7046_, 0);
                            v_val_7048_ = crate::leanh::lean_ctor_get(v___x_7046_, 1);
                            crate::leanh::lean_inc(v_f_7035_);
                            crate::leanh::lean_inc(v_val_7048_);
                            crate::leanh::lean_inc(v_key_7047_);
                            v___x_7049_ = crate::leanh::lean_apply_3(
                                v_f_7035_,
                                v_b_7039_,
                                v_key_7047_,
                                v_val_7048_,
                            );
                            v___y_7041_ = v___x_7049_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_7050_ = crate::leanh::lean_ctor_get(v___x_7046_, 0);
                            crate::leanh::lean_inc(v_f_7035_);
                            v___x_7051_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7035_, v_node_7050_, v_b_7039_);
                            v___y_7041_ = v___x_7051_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_7041_ = v_b_7039_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_7035_);
                    return v_b_7039_;
                }
            }
            1 => {
                v___x_7042_ = 1usize;
                v___x_7043_ = lean_usize_add(v_i_7037_, v___x_7042_);
                v_i_7037_ = v___x_7043_;
                v_b_7039_ = v___y_7041_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_f_7052_: *mut crate::leanh::LeanObject,
    mut v_as_7053_: *mut crate::leanh::LeanObject,
    mut v_i_7054_: *mut crate::leanh::LeanObject,
    mut v_stop_7055_: *mut crate::leanh::LeanObject,
    mut v_b_7056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7057_: usize = 0;
    let mut v_stop_boxed_7058_: usize = 0;
    let mut v_res_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7057_ = crate::leanh::lean_unbox_usize(v_i_7054_);
    crate::leanh::lean_dec(v_i_7054_);
    v_stop_boxed_7058_ = crate::leanh::lean_unbox_usize(v_stop_7055_);
    crate::leanh::lean_dec(v_stop_7055_);
    v_res_7059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_7052_, v_as_7053_, v_i_boxed_7057_, v_stop_boxed_7058_, v_b_7056_);
    crate::leanh::lean_dec_ref(v_as_7053_);
    return v_res_7059_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_7060_: *mut crate::leanh::LeanObject,
    mut v_x_7061_: *mut crate::leanh::LeanObject,
    mut v_x_7062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7060_, v_x_7061_, v_x_7062_);
    crate::leanh::lean_dec_ref(v_x_7061_);
    return v_res_7063_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(
    mut v_f_7064_: *mut crate::leanh::LeanObject,
    mut v_x1_7065_: *mut crate::leanh::LeanObject,
    mut v_x2_7066_: *mut crate::leanh::LeanObject,
    mut v_x3_7067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7068_ = crate::leanh::lean_apply_3(v_f_7064_, v_x1_7065_, v_x2_7066_, v_x3_7067_);
    return v___x_7068_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(
    mut v_map_7069_: *mut crate::leanh::LeanObject,
    mut v_f_7070_: *mut crate::leanh::LeanObject,
    mut v_init_7071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7072_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_7072_, 0, v_f_7070_);
    v___x_7073_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_7072_, v_map_7069_, v_init_7071_);
    return v___x_7073_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(
    mut v_map_7074_: *mut crate::leanh::LeanObject,
    mut v_f_7075_: *mut crate::leanh::LeanObject,
    mut v_init_7076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7077_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_7074_, v_f_7075_, v_init_7076_);
    crate::leanh::lean_dec_ref(v_map_7074_);
    return v_res_7077_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(
    mut v_ps_7078_: *mut crate::leanh::LeanObject,
    mut v_k_7079_: *mut crate::leanh::LeanObject,
    mut v_v_7080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7081_, 0, v_k_7079_);
    crate::leanh::lean_ctor_set(v___x_7081_, 1, v_v_7080_);
    v___x_7082_ = lean_array_push(v_ps_7078_, v___x_7081_);
    return v___x_7082_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(
    mut v_m_7086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7087_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0;
    v___x_7088_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1;
    v___x_7089_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_7086_, v___f_7087_, v___x_7088_);
    return v___x_7089_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(
    mut v_m_7090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7091_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_7090_);
    crate::leanh::lean_dec_ref(v_m_7090_);
    return v_res_7091_;
}
pub unsafe fn l_Lean_Server_partialLspRequestHandlerMethods() -> *mut crate::leanh::LeanObject {
    let mut v___x_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7093_ = l_Lean_Server_statefulRequestHandlers;
    v___x_7094_ = lean_st_ref_get(v___x_7093_);
    v___x_7095_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_7094_);
    crate::leanh::lean_dec(v___x_7094_);
    v___x_7096_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7097_ = lean_array_get_size(v___x_7095_);
    v___x_7098_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(
        v___x_7095_,
        v___x_7096_,
        v___x_7097_,
    );
    crate::leanh::lean_dec_ref(v___x_7095_);
    v___x_7099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7099_, 0, v___x_7098_);
    return v___x_7099_;
}
pub unsafe fn l_Lean_Server_partialLspRequestHandlerMethods___boxed(
    mut v_a_7100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7101_ = l_Lean_Server_partialLspRequestHandlerMethods();
    return v_res_7101_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(
    mut v_00_u03b2_7102_: *mut crate::leanh::LeanObject,
    mut v_m_7103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7104_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_7103_);
    return v___x_7104_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(
    mut v_00_u03b2_7105_: *mut crate::leanh::LeanObject,
    mut v_m_7106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7107_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_7105_, v_m_7106_);
    crate::leanh::lean_dec_ref(v_m_7106_);
    return v_res_7107_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(
    mut v_00_u03c3_7108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7109_: *mut crate::leanh::LeanObject,
    mut v_map_7110_: *mut crate::leanh::LeanObject,
    mut v_f_7111_: *mut crate::leanh::LeanObject,
    mut v_init_7112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7113_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_7110_, v_f_7111_, v_init_7112_);
    return v___x_7113_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(
    mut v_00_u03c3_7114_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7115_: *mut crate::leanh::LeanObject,
    mut v_map_7116_: *mut crate::leanh::LeanObject,
    mut v_f_7117_: *mut crate::leanh::LeanObject,
    mut v_init_7118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7119_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_7114_, v_00_u03b2_7115_, v_map_7116_, v_f_7117_, v_init_7118_);
    crate::leanh::lean_dec_ref(v_map_7116_);
    return v_res_7119_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(
    mut v_map_7120_: *mut crate::leanh::LeanObject,
    mut v_f_7121_: *mut crate::leanh::LeanObject,
    mut v_init_7122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7123_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7121_, v_map_7120_, v_init_7122_);
    return v___x_7123_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_map_7124_: *mut crate::leanh::LeanObject,
    mut v_f_7125_: *mut crate::leanh::LeanObject,
    mut v_init_7126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7127_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_7124_, v_f_7125_, v_init_7126_);
    crate::leanh::lean_dec_ref(v_map_7124_);
    return v_res_7127_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(
    mut v_00_u03c3_7128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7129_: *mut crate::leanh::LeanObject,
    mut v_map_7130_: *mut crate::leanh::LeanObject,
    mut v_f_7131_: *mut crate::leanh::LeanObject,
    mut v_init_7132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7133_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7131_, v_map_7130_, v_init_7132_);
    return v___x_7133_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_7134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7135_: *mut crate::leanh::LeanObject,
    mut v_map_7136_: *mut crate::leanh::LeanObject,
    mut v_f_7137_: *mut crate::leanh::LeanObject,
    mut v_init_7138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7139_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_7134_, v_00_u03b2_7135_, v_map_7136_, v_f_7137_, v_init_7138_);
    crate::leanh::lean_dec_ref(v_map_7136_);
    return v_res_7139_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03c3_7140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7141_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7142_: *mut crate::leanh::LeanObject,
    mut v_f_7143_: *mut crate::leanh::LeanObject,
    mut v_x_7144_: *mut crate::leanh::LeanObject,
    mut v_x_7145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7146_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7143_, v_x_7144_, v_x_7145_);
    return v___x_7146_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03c3_7147_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7148_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7149_: *mut crate::leanh::LeanObject,
    mut v_f_7150_: *mut crate::leanh::LeanObject,
    mut v_x_7151_: *mut crate::leanh::LeanObject,
    mut v_x_7152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7153_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_7147_, v_00_u03b1_7148_, v_00_u03b2_7149_, v_f_7150_, v_x_7151_, v_x_7152_);
    crate::leanh::lean_dec_ref(v_x_7151_);
    return v_res_7153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b1_7154_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7155_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_7156_: *mut crate::leanh::LeanObject,
    mut v_f_7157_: *mut crate::leanh::LeanObject,
    mut v_as_7158_: *mut crate::leanh::LeanObject,
    mut v_i_7159_: usize,
    mut v_stop_7160_: usize,
    mut v_b_7161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_7157_, v_as_7158_, v_i_7159_, v_stop_7160_, v_b_7161_);
    return v___x_7162_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b1_7163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7164_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_7165_: *mut crate::leanh::LeanObject,
    mut v_f_7166_: *mut crate::leanh::LeanObject,
    mut v_as_7167_: *mut crate::leanh::LeanObject,
    mut v_i_7168_: *mut crate::leanh::LeanObject,
    mut v_stop_7169_: *mut crate::leanh::LeanObject,
    mut v_b_7170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7171_: usize = 0;
    let mut v_stop_boxed_7172_: usize = 0;
    let mut v_res_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7171_ = crate::leanh::lean_unbox_usize(v_i_7168_);
    crate::leanh::lean_dec(v_i_7168_);
    v_stop_boxed_7172_ = crate::leanh::lean_unbox_usize(v_stop_7169_);
    crate::leanh::lean_dec(v_stop_7169_);
    v_res_7173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_7163_, v_00_u03b2_7164_, v_00_u03c3_7165_, v_f_7166_, v_as_7167_, v_i_boxed_7171_, v_stop_boxed_7172_, v_b_7170_);
    crate::leanh::lean_dec_ref(v_as_7167_);
    return v_res_7173_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03c3_7174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7176_: *mut crate::leanh::LeanObject,
    mut v_f_7177_: *mut crate::leanh::LeanObject,
    mut v_keys_7178_: *mut crate::leanh::LeanObject,
    mut v_vals_7179_: *mut crate::leanh::LeanObject,
    mut v_heq_7180_: *mut crate::leanh::LeanObject,
    mut v_i_7181_: *mut crate::leanh::LeanObject,
    mut v_acc_7182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_7177_, v_keys_7178_, v_vals_7179_, v_i_7181_, v_acc_7182_);
    return v___x_7183_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03c3_7184_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7186_: *mut crate::leanh::LeanObject,
    mut v_f_7187_: *mut crate::leanh::LeanObject,
    mut v_keys_7188_: *mut crate::leanh::LeanObject,
    mut v_vals_7189_: *mut crate::leanh::LeanObject,
    mut v_heq_7190_: *mut crate::leanh::LeanObject,
    mut v_i_7191_: *mut crate::leanh::LeanObject,
    mut v_acc_7192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_7184_, v_00_u03b1_7185_, v_00_u03b2_7186_, v_f_7187_, v_keys_7188_, v_vals_7189_, v_heq_7190_, v_i_7191_, v_acc_7192_);
    crate::leanh::lean_dec_ref(v_vals_7189_);
    crate::leanh::lean_dec_ref(v_keys_7188_);
    return v_res_7193_;
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(
    mut v_inst_7194_: *mut crate::leanh::LeanObject,
    mut v_pureOnDidChange_7195_: *mut crate::leanh::LeanObject,
    mut v_method_7196_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7197_: *mut crate::leanh::LeanObject,
    mut v_p_7198_: *mut crate::leanh::LeanObject,
    mut v___y_7199_: *mut crate::leanh::LeanObject,
    mut v___y_7200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7212_: u8 = 0;
    let mut v_snd_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7224_: u8 = 0;
    let mut v_unused_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7226_: u8 = 0;
    let mut v_a_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7230_: u8 = 0;
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7234_: u8 = 0;
    let mut v_a_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7238_: u8 = 0;
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_inst_7194_);
                v___x_7202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7202_, 0, v_inst_7194_);
                crate::leanh::lean_ctor_set(v___x_7202_, 1, v___y_7199_);
                crate::leanh::lean_inc_ref(v___y_7200_);
                crate::leanh::lean_inc_ref(v_p_7198_);
                v___x_7203_ = crate::leanh::lean_apply_4(
                    v_pureOnDidChange_7195_,
                    v_p_7198_,
                    v___x_7202_,
                    v___y_7200_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7203_) == 0 {
                    v_a_7204_ = crate::leanh::lean_ctor_get(v___x_7203_, 0);
                    crate::leanh::lean_inc(v_a_7204_);
                    crate::leanh::lean_dec_ref_known(v___x_7203_, 1);
                    v_snd_7205_ = crate::leanh::lean_ctor_get(v_a_7204_, 1);
                    crate::leanh::lean_inc(v_snd_7205_);
                    crate::leanh::lean_dec(v_a_7204_);
                    v___x_7206_ =
                        l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
                            v_method_7196_,
                            v_snd_7205_,
                            v_inst_7194_,
                        );
                    crate::leanh::lean_dec(v_inst_7194_);
                    crate::leanh::lean_dec(v_snd_7205_);
                    if crate::leanh::lean_obj_tag(v___x_7206_) == 0 {
                        v_a_7207_ = crate::leanh::lean_ctor_get(v___x_7206_, 0);
                        crate::leanh::lean_inc(v_a_7207_);
                        crate::leanh::lean_dec_ref_known(v___x_7206_, 1);
                        crate::leanh::lean_inc_ref(v___y_7200_);
                        v___x_7208_ = crate::leanh::lean_apply_4(
                            v_onDidChange_7197_,
                            v_p_7198_,
                            v_a_7207_,
                            v___y_7200_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_7208_) == 0 {
                            v_a_7209_ = crate::leanh::lean_ctor_get(v___x_7208_, 0);
                            v_isSharedCheck_7226_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7208_)) as u8;
                            if v_isSharedCheck_7226_ == 0 {
                                v___x_7211_ = v___x_7208_;
                                v_isShared_7212_ = v_isSharedCheck_7226_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7209_);
                                crate::leanh::lean_dec(v___x_7208_);
                                v___x_7211_ = crate::leanh::lean_box(0);
                                v_isShared_7212_ = v_isSharedCheck_7226_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_7208_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_7198_);
                        crate::leanh::lean_dec_ref(v_onDidChange_7197_);
                        v_a_7227_ = crate::leanh::lean_ctor_get(v___x_7206_, 0);
                        v_isSharedCheck_7234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7206_)) as u8;
                        if v_isSharedCheck_7234_ == 0 {
                            v___x_7229_ = v___x_7206_;
                            v_isShared_7230_ = v_isSharedCheck_7234_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7227_);
                            crate::leanh::lean_dec(v___x_7206_);
                            v___x_7229_ = crate::leanh::lean_box(0);
                            v_isShared_7230_ = v_isSharedCheck_7234_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_7198_);
                    crate::leanh::lean_dec_ref(v_onDidChange_7197_);
                    crate::leanh::lean_dec(v_inst_7194_);
                    v_a_7235_ = crate::leanh::lean_ctor_get(v___x_7203_, 0);
                    v_isSharedCheck_7242_ = (!crate::leanh::lean_is_exclusive(v___x_7203_)) as u8;
                    if v_isSharedCheck_7242_ == 0 {
                        v___x_7237_ = v___x_7203_;
                        v_isShared_7238_ = v_isSharedCheck_7242_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7235_);
                        crate::leanh::lean_dec(v___x_7203_);
                        v___x_7237_ = crate::leanh::lean_box(0);
                        v_isShared_7238_ = v_isSharedCheck_7242_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_7213_ = crate::leanh::lean_ctor_get(v_a_7209_, 1);
                v_isSharedCheck_7224_ = (!crate::leanh::lean_is_exclusive(v_a_7209_)) as u8;
                if v_isSharedCheck_7224_ == 0 {
                    v_unused_7225_ = crate::leanh::lean_ctor_get(v_a_7209_, 0);
                    crate::leanh::lean_dec(v_unused_7225_);
                    v___x_7215_ = v_a_7209_;
                    v_isShared_7216_ = v_isSharedCheck_7224_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7213_);
                    crate::leanh::lean_dec(v_a_7209_);
                    v___x_7215_ = crate::leanh::lean_box(0);
                    v_isShared_7216_ = v_isSharedCheck_7224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7217_ = crate::leanh::lean_box(0);
                if v_isShared_7216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7215_, 0, v___x_7217_);
                    v___x_7219_ = v___x_7215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7223_, 0, v___x_7217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7223_, 1, v_snd_7213_);
                    v___x_7219_ = v_reuseFailAlloc_7223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7211_, 0, v___x_7219_);
                    v___x_7221_ = v___x_7211_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 0, v___x_7219_);
                    v___x_7221_ = v_reuseFailAlloc_7222_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7221_;
            }
            5 => {
                if v_isShared_7230_ == 0 {
                    v___x_7232_ = v___x_7229_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7233_, 0, v_a_7227_);
                    v___x_7232_ = v_reuseFailAlloc_7233_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7232_;
            }
            7 => {
                if v_isShared_7238_ == 0 {
                    v___x_7240_ = v___x_7237_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v_a_7235_);
                    v___x_7240_ = v_reuseFailAlloc_7241_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(
    mut v_inst_7243_: *mut crate::leanh::LeanObject,
    mut v_pureOnDidChange_7244_: *mut crate::leanh::LeanObject,
    mut v_method_7245_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7246_: *mut crate::leanh::LeanObject,
    mut v_p_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7251_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(
        v_inst_7243_,
        v_pureOnDidChange_7244_,
        v_method_7245_,
        v_onDidChange_7246_,
        v_p_7247_,
        v___y_7248_,
        v___y_7249_,
    );
    crate::leanh::lean_dec_ref(v___y_7249_);
    crate::leanh::lean_dec_ref(v_method_7245_);
    return v_res_7251_;
}
pub unsafe fn _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7253_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0;
    v___x_7254_ = l_Lean_Server_RequestError_internalError(v___x_7253_);
    return v___x_7254_;
}
pub unsafe fn _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7256_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2;
    v___x_7257_ = l_Lean_Server_RequestError_internalError(v___x_7256_);
    return v___x_7257_;
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(
    mut v_inst_7258_: *mut crate::leanh::LeanObject,
    mut v_inst_7259_: *mut crate::leanh::LeanObject,
    mut v_pureHandle_7260_: *mut crate::leanh::LeanObject,
    mut v_inst_7261_: *mut crate::leanh::LeanObject,
    mut v_method_7262_: *mut crate::leanh::LeanObject,
    mut v_handler_7263_: *mut crate::leanh::LeanObject,
    mut v_p_7264_: *mut crate::leanh::LeanObject,
    mut v_s_7265_: *mut crate::leanh::LeanObject,
    mut v___y_7266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7274_: u8 = 0;
    let mut v_fst_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_response_x3f_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serialized_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isComplete_7279_: u8 = 0;
    let mut v_a_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7291_: u8 = 0;
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7295_: u8 = 0;
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7305_: u8 = 0;
    let mut v_a_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7309_: u8 = 0;
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_p_7264_);
                v___x_7268_ = crate::leanh::lean_apply_1(v_inst_7258_, v_p_7264_);
                crate::leanh::lean_inc(v_inst_7259_);
                v___x_7269_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7269_, 0, v_inst_7259_);
                crate::leanh::lean_ctor_set(v___x_7269_, 1, v_s_7265_);
                crate::leanh::lean_inc_ref(v___y_7266_);
                v___x_7270_ = crate::leanh::lean_apply_4(
                    v_pureHandle_7260_,
                    v___x_7268_,
                    v___x_7269_,
                    v___y_7266_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7270_) == 0 {
                    v_a_7271_ = crate::leanh::lean_ctor_get(v___x_7270_, 0);
                    v_isSharedCheck_7305_ = (!crate::leanh::lean_is_exclusive(v___x_7270_)) as u8;
                    if v_isSharedCheck_7305_ == 0 {
                        v___x_7273_ = v___x_7270_;
                        v_isShared_7274_ = v_isSharedCheck_7305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7271_);
                        crate::leanh::lean_dec(v___x_7270_);
                        v___x_7273_ = crate::leanh::lean_box(0);
                        v_isShared_7274_ = v_isSharedCheck_7305_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_7264_);
                    crate::leanh::lean_dec_ref(v_handler_7263_);
                    crate::leanh::lean_dec_ref(v_inst_7261_);
                    crate::leanh::lean_dec(v_inst_7259_);
                    v_a_7306_ = crate::leanh::lean_ctor_get(v___x_7270_, 0);
                    v_isSharedCheck_7313_ = (!crate::leanh::lean_is_exclusive(v___x_7270_)) as u8;
                    if v_isSharedCheck_7313_ == 0 {
                        v___x_7308_ = v___x_7270_;
                        v_isShared_7309_ = v_isSharedCheck_7313_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7306_);
                        crate::leanh::lean_dec(v___x_7270_);
                        v___x_7308_ = crate::leanh::lean_box(0);
                        v_isShared_7309_ = v_isSharedCheck_7313_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7275_ = crate::leanh::lean_ctor_get(v_a_7271_, 0);
                crate::leanh::lean_inc(v_fst_7275_);
                v_snd_7276_ = crate::leanh::lean_ctor_get(v_a_7271_, 1);
                crate::leanh::lean_inc(v_snd_7276_);
                crate::leanh::lean_dec(v_a_7271_);
                v_response_x3f_7277_ = crate::leanh::lean_ctor_get(v_fst_7275_, 0);
                crate::leanh::lean_inc(v_response_x3f_7277_);
                v_serialized_7278_ = crate::leanh::lean_ctor_get(v_fst_7275_, 1);
                crate::leanh::lean_inc_ref(v_serialized_7278_);
                v_isComplete_7279_ = crate::leanh::lean_ctor_get_uint8(
                    v_fst_7275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec(v_fst_7275_);
                if crate::leanh::lean_obj_tag(v_response_x3f_7277_) == 0 {
                    v___x_7300_ = l_Lean_Json_parse(v_serialized_7278_);
                    if crate::leanh::lean_obj_tag(v___x_7300_) == 1 {
                        v_a_7301_ = crate::leanh::lean_ctor_get(v___x_7300_, 0);
                        crate::leanh::lean_inc(v_a_7301_);
                        crate::leanh::lean_dec_ref_known(v___x_7300_, 1);
                        v_a_7281_ = v_a_7301_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7300_);
                        crate::leanh::lean_dec(v_snd_7276_);
                        crate::leanh::lean_del_object(v___x_7273_);
                        crate::leanh::lean_dec(v_p_7264_);
                        crate::leanh::lean_dec_ref(v_handler_7263_);
                        crate::leanh::lean_dec_ref(v_inst_7261_);
                        crate::leanh::lean_dec(v_inst_7259_);
                        v___x_7302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once), _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
                        v___x_7303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7303_, 0, v___x_7302_);
                        return v___x_7303_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_serialized_7278_);
                    v_val_7304_ = crate::leanh::lean_ctor_get(v_response_x3f_7277_, 0);
                    crate::leanh::lean_inc(v_val_7304_);
                    crate::leanh::lean_dec_ref_known(v_response_x3f_7277_, 1);
                    v_a_7281_ = v_val_7304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7282_ = crate::leanh::lean_apply_1(v_inst_7261_, v_a_7281_);
                if crate::leanh::lean_obj_tag(v___x_7282_) == 1 {
                    crate::leanh::lean_del_object(v___x_7273_);
                    v_a_7283_ = crate::leanh::lean_ctor_get(v___x_7282_, 0);
                    crate::leanh::lean_inc(v_a_7283_);
                    crate::leanh::lean_dec_ref_known(v___x_7282_, 1);
                    v___x_7284_ =
                        l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(
                            v_method_7262_,
                            v_snd_7276_,
                            v_inst_7259_,
                        );
                    crate::leanh::lean_dec(v_inst_7259_);
                    crate::leanh::lean_dec(v_snd_7276_);
                    if crate::leanh::lean_obj_tag(v___x_7284_) == 0 {
                        v_a_7285_ = crate::leanh::lean_ctor_get(v___x_7284_, 0);
                        crate::leanh::lean_inc(v_a_7285_);
                        crate::leanh::lean_dec_ref_known(v___x_7284_, 1);
                        v___x_7286_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_7286_, 0, v_a_7283_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7286_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_isComplete_7279_,
                        );
                        crate::leanh::lean_inc_ref(v___y_7266_);
                        v___x_7287_ = crate::leanh::lean_apply_5(
                            v_handler_7263_,
                            v_p_7264_,
                            v___x_7286_,
                            v_a_7285_,
                            v___y_7266_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_7287_;
                    } else {
                        crate::leanh::lean_dec(v_a_7283_);
                        crate::leanh::lean_dec(v_p_7264_);
                        crate::leanh::lean_dec_ref(v_handler_7263_);
                        v_a_7288_ = crate::leanh::lean_ctor_get(v___x_7284_, 0);
                        v_isSharedCheck_7295_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7284_)) as u8;
                        if v_isSharedCheck_7295_ == 0 {
                            v___x_7290_ = v___x_7284_;
                            v_isShared_7291_ = v_isSharedCheck_7295_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7288_);
                            crate::leanh::lean_dec(v___x_7284_);
                            v___x_7290_ = crate::leanh::lean_box(0);
                            v_isShared_7291_ = v_isSharedCheck_7295_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7282_);
                    crate::leanh::lean_dec(v_snd_7276_);
                    crate::leanh::lean_dec(v_p_7264_);
                    crate::leanh::lean_dec_ref(v_handler_7263_);
                    crate::leanh::lean_dec(v_inst_7259_);
                    v___x_7296_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once), _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
                    if v_isShared_7274_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7273_, 1);
                        crate::leanh::lean_ctor_set(v___x_7273_, 0, v___x_7296_);
                        v___x_7298_ = v___x_7273_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7299_, 0, v___x_7296_);
                        v___x_7298_ = v_reuseFailAlloc_7299_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7291_ == 0 {
                    v___x_7293_ = v___x_7290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7294_, 0, v_a_7288_);
                    v___x_7293_ = v_reuseFailAlloc_7294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7293_;
            }
            5 => {
                return v___x_7298_;
            }
            6 => {
                if v_isShared_7309_ == 0 {
                    v___x_7311_ = v___x_7308_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7312_, 0, v_a_7306_);
                    v___x_7311_ = v_reuseFailAlloc_7312_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(
    mut v_inst_7314_: *mut crate::leanh::LeanObject,
    mut v_inst_7315_: *mut crate::leanh::LeanObject,
    mut v_pureHandle_7316_: *mut crate::leanh::LeanObject,
    mut v_inst_7317_: *mut crate::leanh::LeanObject,
    mut v_method_7318_: *mut crate::leanh::LeanObject,
    mut v_handler_7319_: *mut crate::leanh::LeanObject,
    mut v_p_7320_: *mut crate::leanh::LeanObject,
    mut v_s_7321_: *mut crate::leanh::LeanObject,
    mut v___y_7322_: *mut crate::leanh::LeanObject,
    mut v___y_7323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7324_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(
        v_inst_7314_,
        v_inst_7315_,
        v_pureHandle_7316_,
        v_inst_7317_,
        v_method_7318_,
        v_handler_7319_,
        v_p_7320_,
        v_s_7321_,
        v___y_7322_,
    );
    crate::leanh::lean_dec_ref(v___y_7322_);
    crate::leanh::lean_dec_ref(v_method_7318_);
    return v_res_7324_;
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg(
    mut v_method_7326_: *mut crate::leanh::LeanObject,
    mut v_inst_7327_: *mut crate::leanh::LeanObject,
    mut v_inst_7328_: *mut crate::leanh::LeanObject,
    mut v_inst_7329_: *mut crate::leanh::LeanObject,
    mut v_inst_7330_: *mut crate::leanh::LeanObject,
    mut v_inst_7331_: *mut crate::leanh::LeanObject,
    mut v_inst_7332_: *mut crate::leanh::LeanObject,
    mut v_handler_7333_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7340_: u8 = 0;
    let mut v___x_7341_: u8 = 0;
    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureHandle_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureOnDidChange_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initState_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_completeness_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7364_: u8 = 0;
    let mut v___x_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7368_: u8 = 0;
    let mut v___x_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7377_: u8 = 0;
    let mut v_a_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7381_: u8 = 0;
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7336_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_7336_) == 0 {
                    v_a_7337_ = crate::leanh::lean_ctor_get(v___x_7336_, 0);
                    v_isSharedCheck_7377_ = (!crate::leanh::lean_is_exclusive(v___x_7336_)) as u8;
                    if v_isSharedCheck_7377_ == 0 {
                        v___x_7339_ = v___x_7336_;
                        v_isShared_7340_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7337_);
                        crate::leanh::lean_dec(v___x_7336_);
                        v___x_7339_ = crate::leanh::lean_box(0);
                        v_isShared_7340_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_onDidChange_7334_);
                    crate::leanh::lean_dec_ref(v_handler_7333_);
                    crate::leanh::lean_dec(v_inst_7332_);
                    crate::leanh::lean_dec_ref(v_inst_7331_);
                    crate::leanh::lean_dec_ref(v_inst_7330_);
                    crate::leanh::lean_dec_ref(v_inst_7329_);
                    crate::leanh::lean_dec_ref(v_inst_7328_);
                    crate::leanh::lean_dec_ref(v_inst_7327_);
                    crate::leanh::lean_dec_ref(v_method_7326_);
                    v_a_7378_ = crate::leanh::lean_ctor_get(v___x_7336_, 0);
                    v_isSharedCheck_7385_ = (!crate::leanh::lean_is_exclusive(v___x_7336_)) as u8;
                    if v_isSharedCheck_7385_ == 0 {
                        v___x_7380_ = v___x_7336_;
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7378_);
                        crate::leanh::lean_dec(v___x_7336_);
                        v___x_7380_ = crate::leanh::lean_box(0);
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7341_ = (crate::leanh::lean_unbox(v_a_7337_) as u8);
                crate::leanh::lean_dec(v_a_7337_);
                if v___x_7341_ == 0 {
                    crate::leanh::lean_dec_ref(v_onDidChange_7334_);
                    crate::leanh::lean_dec_ref(v_handler_7333_);
                    crate::leanh::lean_dec(v_inst_7332_);
                    crate::leanh::lean_dec_ref(v_inst_7331_);
                    crate::leanh::lean_dec_ref(v_inst_7330_);
                    crate::leanh::lean_dec_ref(v_inst_7329_);
                    crate::leanh::lean_dec_ref(v_inst_7328_);
                    crate::leanh::lean_dec_ref(v_inst_7327_);
                    v___x_7342_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0;
                    v___x_7343_ = lean_string_append(v___x_7342_, v_method_7326_);
                    crate::leanh::lean_dec_ref(v_method_7326_);
                    v___x_7344_ = l_Lean_Server_registerLspRequestHandler___redArg___closed__1;
                    v___x_7345_ = lean_string_append(v___x_7343_, v___x_7344_);
                    v___x_7346_ = lean_mk_io_user_error(v___x_7345_);
                    if v_isShared_7340_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7339_, 1);
                        crate::leanh::lean_ctor_set(v___x_7339_, 0, v___x_7346_);
                        v___x_7348_ = v___x_7339_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7349_, 0, v___x_7346_);
                        v___x_7348_ = v_reuseFailAlloc_7349_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7350_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_7326_);
                    if crate::leanh::lean_obj_tag(v___x_7350_) == 1 {
                        crate::leanh::lean_del_object(v___x_7339_);
                        v_val_7351_ = crate::leanh::lean_ctor_get(v___x_7350_, 0);
                        crate::leanh::lean_inc(v_val_7351_);
                        crate::leanh::lean_dec_ref_known(v___x_7350_, 1);
                        v_pureHandle_7352_ = crate::leanh::lean_ctor_get(v_val_7351_, 1);
                        crate::leanh::lean_inc_ref(v_pureHandle_7352_);
                        v_pureOnDidChange_7353_ = crate::leanh::lean_ctor_get(v_val_7351_, 3);
                        crate::leanh::lean_inc_ref(v_pureOnDidChange_7353_);
                        v_initState_7354_ = crate::leanh::lean_ctor_get(v_val_7351_, 6);
                        crate::leanh::lean_inc(v_initState_7354_);
                        v_completeness_7355_ = crate::leanh::lean_ctor_get(v_val_7351_, 8);
                        crate::leanh::lean_inc(v_completeness_7355_);
                        crate::leanh::lean_dec(v_val_7351_);
                        v___x_7356_ =
                            l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(
                                v_method_7326_,
                                v_initState_7354_,
                                v_inst_7332_,
                            );
                        crate::leanh::lean_dec(v_initState_7354_);
                        if crate::leanh::lean_obj_tag(v___x_7356_) == 0 {
                            v_a_7357_ = crate::leanh::lean_ctor_get(v___x_7356_, 0);
                            crate::leanh::lean_inc(v_a_7357_);
                            crate::leanh::lean_dec_ref_known(v___x_7356_, 1);
                            crate::leanh::lean_inc_ref_n(v_method_7326_, 2);
                            crate::leanh::lean_inc_n(v_inst_7332_, 2);
                            v___f_7358_ = crate::leanh::lean_alloc_closure(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 4);
                            crate::leanh::lean_closure_set(v___f_7358_, 0, v_inst_7332_);
                            crate::leanh::lean_closure_set(v___f_7358_, 1, v_pureOnDidChange_7353_);
                            crate::leanh::lean_closure_set(v___f_7358_, 2, v_method_7326_);
                            crate::leanh::lean_closure_set(v___f_7358_, 3, v_onDidChange_7334_);
                            v___f_7359_ = crate::leanh::lean_alloc_closure(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 6);
                            crate::leanh::lean_closure_set(v___f_7359_, 0, v_inst_7328_);
                            crate::leanh::lean_closure_set(v___f_7359_, 1, v_inst_7332_);
                            crate::leanh::lean_closure_set(v___f_7359_, 2, v_pureHandle_7352_);
                            crate::leanh::lean_closure_set(v___f_7359_, 3, v_inst_7330_);
                            crate::leanh::lean_closure_set(v___f_7359_, 4, v_method_7326_);
                            crate::leanh::lean_closure_set(v___f_7359_, 5, v_handler_7333_);
                            v___x_7360_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_7326_, v_completeness_7355_, v_inst_7327_, v_inst_7329_, v_inst_7331_, v_inst_7332_, v_a_7357_, v___f_7359_, v___f_7358_);
                            return v___x_7360_;
                        } else {
                            crate::leanh::lean_dec(v_completeness_7355_);
                            crate::leanh::lean_dec_ref(v_pureOnDidChange_7353_);
                            crate::leanh::lean_dec_ref(v_pureHandle_7352_);
                            crate::leanh::lean_dec_ref(v_onDidChange_7334_);
                            crate::leanh::lean_dec_ref(v_handler_7333_);
                            crate::leanh::lean_dec(v_inst_7332_);
                            crate::leanh::lean_dec_ref(v_inst_7331_);
                            crate::leanh::lean_dec_ref(v_inst_7330_);
                            crate::leanh::lean_dec_ref(v_inst_7329_);
                            crate::leanh::lean_dec_ref(v_inst_7328_);
                            crate::leanh::lean_dec_ref(v_inst_7327_);
                            crate::leanh::lean_dec_ref(v_method_7326_);
                            v_a_7361_ = crate::leanh::lean_ctor_get(v___x_7356_, 0);
                            v_isSharedCheck_7368_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7356_)) as u8;
                            if v_isSharedCheck_7368_ == 0 {
                                v___x_7363_ = v___x_7356_;
                                v_isShared_7364_ = v_isSharedCheck_7368_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7361_);
                                crate::leanh::lean_dec(v___x_7356_);
                                v___x_7363_ = crate::leanh::lean_box(0);
                                v_isShared_7364_ = v_isSharedCheck_7368_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7350_);
                        crate::leanh::lean_dec_ref(v_onDidChange_7334_);
                        crate::leanh::lean_dec_ref(v_handler_7333_);
                        crate::leanh::lean_dec(v_inst_7332_);
                        crate::leanh::lean_dec_ref(v_inst_7331_);
                        crate::leanh::lean_dec_ref(v_inst_7330_);
                        crate::leanh::lean_dec_ref(v_inst_7329_);
                        crate::leanh::lean_dec_ref(v_inst_7328_);
                        crate::leanh::lean_dec_ref(v_inst_7327_);
                        v___x_7369_ =
                            l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0;
                        v___x_7370_ = lean_string_append(v___x_7369_, v_method_7326_);
                        crate::leanh::lean_dec_ref(v_method_7326_);
                        v___x_7371_ = l_Lean_Server_chainLspRequestHandler___redArg___closed__1;
                        v___x_7372_ = lean_string_append(v___x_7370_, v___x_7371_);
                        v___x_7373_ = lean_mk_io_user_error(v___x_7372_);
                        if v_isShared_7340_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_7339_, 1);
                            crate::leanh::lean_ctor_set(v___x_7339_, 0, v___x_7373_);
                            v___x_7375_ = v___x_7339_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_7376_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7376_, 0, v___x_7373_);
                            v___x_7375_ = v_reuseFailAlloc_7376_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7348_;
            }
            3 => {
                if v_isShared_7364_ == 0 {
                    v___x_7366_ = v___x_7363_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7367_, 0, v_a_7361_);
                    v___x_7366_ = v_reuseFailAlloc_7367_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7366_;
            }
            5 => {
                return v___x_7375_;
            }
            6 => {
                if v_isShared_7381_ == 0 {
                    v___x_7383_ = v___x_7380_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7384_, 0, v_a_7378_);
                    v___x_7383_ = v_reuseFailAlloc_7384_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(
    mut v_method_7386_: *mut crate::leanh::LeanObject,
    mut v_inst_7387_: *mut crate::leanh::LeanObject,
    mut v_inst_7388_: *mut crate::leanh::LeanObject,
    mut v_inst_7389_: *mut crate::leanh::LeanObject,
    mut v_inst_7390_: *mut crate::leanh::LeanObject,
    mut v_inst_7391_: *mut crate::leanh::LeanObject,
    mut v_inst_7392_: *mut crate::leanh::LeanObject,
    mut v_handler_7393_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7394_: *mut crate::leanh::LeanObject,
    mut v_a_7395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7396_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(
        v_method_7386_,
        v_inst_7387_,
        v_inst_7388_,
        v_inst_7389_,
        v_inst_7390_,
        v_inst_7391_,
        v_inst_7392_,
        v_handler_7393_,
        v_onDidChange_7394_,
    );
    return v_res_7396_;
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler(
    mut v_method_7397_: *mut crate::leanh::LeanObject,
    mut v_paramType_7398_: *mut crate::leanh::LeanObject,
    mut v_inst_7399_: *mut crate::leanh::LeanObject,
    mut v_inst_7400_: *mut crate::leanh::LeanObject,
    mut v_inst_7401_: *mut crate::leanh::LeanObject,
    mut v_respType_7402_: *mut crate::leanh::LeanObject,
    mut v_inst_7403_: *mut crate::leanh::LeanObject,
    mut v_inst_7404_: *mut crate::leanh::LeanObject,
    mut v_stateType_7405_: *mut crate::leanh::LeanObject,
    mut v_inst_7406_: *mut crate::leanh::LeanObject,
    mut v_handler_7407_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7410_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(
        v_method_7397_,
        v_inst_7399_,
        v_inst_7400_,
        v_inst_7401_,
        v_inst_7403_,
        v_inst_7404_,
        v_inst_7406_,
        v_handler_7407_,
        v_onDidChange_7408_,
    );
    return v___x_7410_;
}
pub unsafe fn l_Lean_Server_chainStatefulLspRequestHandler___boxed(
    mut v_method_7411_: *mut crate::leanh::LeanObject,
    mut v_paramType_7412_: *mut crate::leanh::LeanObject,
    mut v_inst_7413_: *mut crate::leanh::LeanObject,
    mut v_inst_7414_: *mut crate::leanh::LeanObject,
    mut v_inst_7415_: *mut crate::leanh::LeanObject,
    mut v_respType_7416_: *mut crate::leanh::LeanObject,
    mut v_inst_7417_: *mut crate::leanh::LeanObject,
    mut v_inst_7418_: *mut crate::leanh::LeanObject,
    mut v_stateType_7419_: *mut crate::leanh::LeanObject,
    mut v_inst_7420_: *mut crate::leanh::LeanObject,
    mut v_handler_7421_: *mut crate::leanh::LeanObject,
    mut v_onDidChange_7422_: *mut crate::leanh::LeanObject,
    mut v_a_7423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7424_ = l_Lean_Server_chainStatefulLspRequestHandler(
        v_method_7411_,
        v_paramType_7412_,
        v_inst_7413_,
        v_inst_7414_,
        v_inst_7415_,
        v_respType_7416_,
        v_inst_7417_,
        v_inst_7418_,
        v_stateType_7419_,
        v_inst_7420_,
        v_handler_7421_,
        v_onDidChange_7422_,
    );
    return v_res_7424_;
}
pub unsafe fn l_Lean_Server_handleOnDidChange___lam__0(
    mut v_p_7425_: *mut crate::leanh::LeanObject,
    mut v_x_7426_: *mut crate::leanh::LeanObject,
    mut v_handler_7427_: *mut crate::leanh::LeanObject,
    mut v___y_7428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onDidChange_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_onDidChange_7430_ = crate::leanh::lean_ctor_get(v_handler_7427_, 4);
    crate::leanh::lean_inc_ref(v_onDidChange_7430_);
    crate::leanh::lean_dec_ref(v_handler_7427_);
    crate::leanh::lean_inc_ref(v___y_7428_);
    v___x_7431_ = crate::leanh::lean_apply_3(
        v_onDidChange_7430_,
        v_p_7425_,
        v___y_7428_,
        crate::leanh::lean_box(0),
    );
    return v___x_7431_;
}
pub unsafe fn l_Lean_Server_handleOnDidChange___lam__0___boxed(
    mut v_p_7432_: *mut crate::leanh::LeanObject,
    mut v_x_7433_: *mut crate::leanh::LeanObject,
    mut v_handler_7434_: *mut crate::leanh::LeanObject,
    mut v___y_7435_: *mut crate::leanh::LeanObject,
    mut v___y_7436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7437_ = l_Lean_Server_handleOnDidChange___lam__0(
        v_p_7432_,
        v_x_7433_,
        v_handler_7434_,
        v___y_7435_,
    );
    crate::leanh::lean_dec_ref(v___y_7435_);
    crate::leanh::lean_dec_ref(v_x_7433_);
    return v_res_7437_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(
    mut v_f_7438_: *mut crate::leanh::LeanObject,
    mut v_x_7439_: *mut crate::leanh::LeanObject,
    mut v___y_7440_: *mut crate::leanh::LeanObject,
    mut v___y_7441_: *mut crate::leanh::LeanObject,
    mut v___y_7442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_7442_);
    v___x_7444_ = crate::leanh::lean_apply_4(
        v_f_7438_,
        v___y_7440_,
        v___y_7441_,
        v___y_7442_,
        crate::leanh::lean_box(0),
    );
    return v___x_7444_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(
    mut v_f_7445_: *mut crate::leanh::LeanObject,
    mut v_x_7446_: *mut crate::leanh::LeanObject,
    mut v___y_7447_: *mut crate::leanh::LeanObject,
    mut v___y_7448_: *mut crate::leanh::LeanObject,
    mut v___y_7449_: *mut crate::leanh::LeanObject,
    mut v___y_7450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7451_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_7445_, v_x_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
    crate::leanh::lean_dec_ref(v___y_7449_);
    return v_res_7451_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_7452_: *mut crate::leanh::LeanObject,
    mut v_keys_7453_: *mut crate::leanh::LeanObject,
    mut v_vals_7454_: *mut crate::leanh::LeanObject,
    mut v_i_7455_: *mut crate::leanh::LeanObject,
    mut v_acc_7456_: *mut crate::leanh::LeanObject,
    mut v___y_7457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7459_ = lean_array_get_size(v_keys_7453_);
                v___x_7460_ = lean_nat_dec_lt(v_i_7455_, v___x_7459_);
                if v___x_7460_ == 0 {
                    crate::leanh::lean_dec(v_i_7455_);
                    crate::leanh::lean_dec_ref(v_f_7452_);
                    v___x_7461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7461_, 0, v_acc_7456_);
                    return v___x_7461_;
                } else {
                    v_k_7462_ = lean_array_fget_borrowed(v_keys_7453_, v_i_7455_);
                    v_v_7463_ = lean_array_fget_borrowed(v_vals_7454_, v_i_7455_);
                    crate::leanh::lean_inc_ref(v_f_7452_);
                    crate::leanh::lean_inc_ref(v___y_7457_);
                    crate::leanh::lean_inc(v_v_7463_);
                    crate::leanh::lean_inc(v_k_7462_);
                    v___x_7464_ = crate::leanh::lean_apply_5(
                        v_f_7452_,
                        v_acc_7456_,
                        v_k_7462_,
                        v_v_7463_,
                        v___y_7457_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7464_) == 0 {
                        v_a_7465_ = crate::leanh::lean_ctor_get(v___x_7464_, 0);
                        crate::leanh::lean_inc(v_a_7465_);
                        crate::leanh::lean_dec_ref_known(v___x_7464_, 1);
                        v___x_7466_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7467_ = lean_nat_add(v_i_7455_, v___x_7466_);
                        crate::leanh::lean_dec(v_i_7455_);
                        v_i_7455_ = v___x_7467_;
                        v_acc_7456_ = v_a_7465_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_7455_);
                        crate::leanh::lean_dec_ref(v_f_7452_);
                        return v___x_7464_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_7469_: *mut crate::leanh::LeanObject,
    mut v_keys_7470_: *mut crate::leanh::LeanObject,
    mut v_vals_7471_: *mut crate::leanh::LeanObject,
    mut v_i_7472_: *mut crate::leanh::LeanObject,
    mut v_acc_7473_: *mut crate::leanh::LeanObject,
    mut v___y_7474_: *mut crate::leanh::LeanObject,
    mut v___y_7475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7469_, v_keys_7470_, v_vals_7471_, v_i_7472_, v_acc_7473_, v___y_7474_);
    crate::leanh::lean_dec_ref(v___y_7474_);
    crate::leanh::lean_dec_ref(v_vals_7471_);
    crate::leanh::lean_dec_ref(v_keys_7470_);
    return v_res_7476_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(
    mut v_f_7477_: *mut crate::leanh::LeanObject,
    mut v_x_7478_: *mut crate::leanh::LeanObject,
    mut v_x_7479_: *mut crate::leanh::LeanObject,
    mut v___y_7480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7485_: u8 = 0;
    let mut v___x_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: u8 = 0;
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7492_: u8 = 0;
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: usize = 0;
    let mut v___x_7497_: usize = 0;
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: usize = 0;
    let mut v___x_7500_: usize = 0;
    let mut v___x_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7502_: u8 = 0;
    let mut v_ks_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7478_) == 0 {
                    v_es_7482_ = crate::leanh::lean_ctor_get(v_x_7478_, 0);
                    v_isSharedCheck_7502_ = (!crate::leanh::lean_is_exclusive(v_x_7478_)) as u8;
                    if v_isSharedCheck_7502_ == 0 {
                        v___x_7484_ = v_x_7478_;
                        v_isShared_7485_ = v_isSharedCheck_7502_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_7482_);
                        crate::leanh::lean_dec(v_x_7478_);
                        v___x_7484_ = crate::leanh::lean_box(0);
                        v_isShared_7485_ = v_isSharedCheck_7502_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_7503_ = crate::leanh::lean_ctor_get(v_x_7478_, 0);
                    crate::leanh::lean_inc_ref(v_ks_7503_);
                    v_vs_7504_ = crate::leanh::lean_ctor_get(v_x_7478_, 1);
                    crate::leanh::lean_inc_ref(v_vs_7504_);
                    crate::leanh::lean_dec_ref_known(v_x_7478_, 2);
                    v___x_7505_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7477_, v_ks_7503_, v_vs_7504_, v___x_7505_, v_x_7479_, v___y_7480_);
                    crate::leanh::lean_dec_ref(v_vs_7504_);
                    crate::leanh::lean_dec_ref(v_ks_7503_);
                    return v___x_7506_;
                }
            }
            1 => {
                v___x_7486_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7487_ = lean_array_get_size(v_es_7482_);
                v___x_7488_ = lean_nat_dec_lt(v___x_7486_, v___x_7487_);
                if v___x_7488_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_7482_);
                    crate::leanh::lean_dec_ref(v_f_7477_);
                    if v_isShared_7485_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7484_, 0, v_x_7479_);
                        v___x_7490_ = v___x_7484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7491_, 0, v_x_7479_);
                        v___x_7490_ = v_reuseFailAlloc_7491_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7492_ = lean_nat_dec_le(v___x_7487_, v___x_7487_);
                    if v___x_7492_ == 0 {
                        if v___x_7488_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_7482_);
                            crate::leanh::lean_dec_ref(v_f_7477_);
                            if v_isShared_7485_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7484_, 0, v_x_7479_);
                                v___x_7494_ = v___x_7484_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_7495_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 0, v_x_7479_);
                                v___x_7494_ = v_reuseFailAlloc_7495_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7484_);
                            v___x_7496_ = 0usize;
                            v___x_7497_ = lean_usize_of_nat(v___x_7487_);
                            v___x_7498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7477_, v_es_7482_, v___x_7496_, v___x_7497_, v_x_7479_, v___y_7480_);
                            crate::leanh::lean_dec_ref(v_es_7482_);
                            return v___x_7498_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7484_);
                        v___x_7499_ = 0usize;
                        v___x_7500_ = lean_usize_of_nat(v___x_7487_);
                        v___x_7501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7477_, v_es_7482_, v___x_7499_, v___x_7500_, v_x_7479_, v___y_7480_);
                        crate::leanh::lean_dec_ref(v_es_7482_);
                        return v___x_7501_;
                    }
                }
            }
            2 => {
                return v___x_7490_;
            }
            3 => {
                return v___x_7494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_f_7507_: *mut crate::leanh::LeanObject,
    mut v_as_7508_: *mut crate::leanh::LeanObject,
    mut v_i_7509_: usize,
    mut v_stop_7510_: usize,
    mut v_b_7511_: *mut crate::leanh::LeanObject,
    mut v___y_7512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: usize = 0;
    let mut v___x_7517_: usize = 0;
    let mut v___y_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: u8 = 0;
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7522_ = lean_usize_dec_eq(v_i_7509_, v_stop_7510_);
                if v___x_7522_ == 0 {
                    v___x_7523_ = lean_array_uget_borrowed(v_as_7508_, v_i_7509_);
                    match crate::leanh::lean_obj_tag(v___x_7523_) {
                        0 => {
                            v_key_7524_ = crate::leanh::lean_ctor_get(v___x_7523_, 0);
                            v_val_7525_ = crate::leanh::lean_ctor_get(v___x_7523_, 1);
                            crate::leanh::lean_inc_ref(v_f_7507_);
                            crate::leanh::lean_inc_ref(v___y_7512_);
                            crate::leanh::lean_inc(v_val_7525_);
                            crate::leanh::lean_inc(v_key_7524_);
                            v___x_7526_ = crate::leanh::lean_apply_5(
                                v_f_7507_,
                                v_b_7511_,
                                v_key_7524_,
                                v_val_7525_,
                                v___y_7512_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_7520_ = v___x_7526_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_7527_ = crate::leanh::lean_ctor_get(v___x_7523_, 0);
                            crate::leanh::lean_inc(v_node_7527_);
                            crate::leanh::lean_inc_ref(v_f_7507_);
                            v___x_7528_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_7507_, v_node_7527_, v_b_7511_, v___y_7512_);
                            v___y_7520_ = v___x_7528_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_7515_ = v_b_7511_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_7507_);
                    v___x_7529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7529_, 0, v_b_7511_);
                    return v___x_7529_;
                }
            }
            1 => {
                v___x_7516_ = 1usize;
                v___x_7517_ = lean_usize_add(v_i_7509_, v___x_7516_);
                v_i_7509_ = v___x_7517_;
                v_b_7511_ = v_a_7515_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_7520_) == 0 {
                    v_a_7521_ = crate::leanh::lean_ctor_get(v___y_7520_, 0);
                    crate::leanh::lean_inc(v_a_7521_);
                    crate::leanh::lean_dec_ref_known(v___y_7520_, 1);
                    v_a_7515_ = v_a_7521_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_7507_);
                    return v___y_7520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_f_7530_: *mut crate::leanh::LeanObject,
    mut v_as_7531_: *mut crate::leanh::LeanObject,
    mut v_i_7532_: *mut crate::leanh::LeanObject,
    mut v_stop_7533_: *mut crate::leanh::LeanObject,
    mut v_b_7534_: *mut crate::leanh::LeanObject,
    mut v___y_7535_: *mut crate::leanh::LeanObject,
    mut v___y_7536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7537_: usize = 0;
    let mut v_stop_boxed_7538_: usize = 0;
    let mut v_res_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7537_ = crate::leanh::lean_unbox_usize(v_i_7532_);
    crate::leanh::lean_dec(v_i_7532_);
    v_stop_boxed_7538_ = crate::leanh::lean_unbox_usize(v_stop_7533_);
    crate::leanh::lean_dec(v_stop_7533_);
    v_res_7539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7530_, v_as_7531_, v_i_boxed_7537_, v_stop_boxed_7538_, v_b_7534_, v___y_7535_);
    crate::leanh::lean_dec_ref(v___y_7535_);
    crate::leanh::lean_dec_ref(v_as_7531_);
    return v_res_7539_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_7540_: *mut crate::leanh::LeanObject,
    mut v_x_7541_: *mut crate::leanh::LeanObject,
    mut v_x_7542_: *mut crate::leanh::LeanObject,
    mut v___y_7543_: *mut crate::leanh::LeanObject,
    mut v___y_7544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7545_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_7540_, v_x_7541_, v_x_7542_, v___y_7543_);
    crate::leanh::lean_dec_ref(v___y_7543_);
    return v_res_7545_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(
    mut v_map_7546_: *mut crate::leanh::LeanObject,
    mut v_f_7547_: *mut crate::leanh::LeanObject,
    mut v___y_7548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7550_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
    crate::leanh::lean_closure_set(v___f_7550_, 0, v_f_7547_);
    v___x_7551_ = crate::leanh::lean_box(0);
    v___x_7552_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_7550_, v_map_7546_, v___x_7551_, v___y_7548_);
    return v___x_7552_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(
    mut v_map_7553_: *mut crate::leanh::LeanObject,
    mut v_f_7554_: *mut crate::leanh::LeanObject,
    mut v___y_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7557_ =
        l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(
            v_map_7553_,
            v_f_7554_,
            v___y_7555_,
        );
    crate::leanh::lean_dec_ref(v___y_7555_);
    return v_res_7557_;
}
pub unsafe fn l_Lean_Server_handleOnDidChange(
    mut v_p_7558_: *mut crate::leanh::LeanObject,
    mut v_a_7559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7561_ = l_Lean_Server_statefulRequestHandlers;
    v___x_7562_ = lean_st_ref_get(v___x_7561_);
    v___f_7563_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_handleOnDidChange___lam__0___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7563_, 0, v_p_7558_);
    v___x_7564_ =
        l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(
            v___x_7562_,
            v___f_7563_,
            v_a_7559_,
        );
    return v___x_7564_;
}
pub unsafe fn l_Lean_Server_handleOnDidChange___boxed(
    mut v_p_7565_: *mut crate::leanh::LeanObject,
    mut v_a_7566_: *mut crate::leanh::LeanObject,
    mut v_a_7567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7568_ = l_Lean_Server_handleOnDidChange(v_p_7565_, v_a_7566_);
    crate::leanh::lean_dec_ref(v_a_7566_);
    return v_res_7568_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(
    mut v_00_u03b2_7569_: *mut crate::leanh::LeanObject,
    mut v_map_7570_: *mut crate::leanh::LeanObject,
    mut v_f_7571_: *mut crate::leanh::LeanObject,
    mut v___y_7572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7574_ =
        l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(
            v_map_7570_,
            v_f_7571_,
            v___y_7572_,
        );
    return v___x_7574_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(
    mut v_00_u03b2_7575_: *mut crate::leanh::LeanObject,
    mut v_map_7576_: *mut crate::leanh::LeanObject,
    mut v_f_7577_: *mut crate::leanh::LeanObject,
    mut v___y_7578_: *mut crate::leanh::LeanObject,
    mut v___y_7579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7580_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(
        v_00_u03b2_7575_,
        v_map_7576_,
        v_f_7577_,
        v___y_7578_,
    );
    crate::leanh::lean_dec_ref(v___y_7578_);
    return v_res_7580_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(
    mut v_map_7581_: *mut crate::leanh::LeanObject,
    mut v_f_7582_: *mut crate::leanh::LeanObject,
    mut v_init_7583_: *mut crate::leanh::LeanObject,
    mut v___y_7584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7586_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_7582_, v_map_7581_, v_init_7583_, v___y_7584_);
    return v___x_7586_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(
    mut v_map_7587_: *mut crate::leanh::LeanObject,
    mut v_f_7588_: *mut crate::leanh::LeanObject,
    mut v_init_7589_: *mut crate::leanh::LeanObject,
    mut v___y_7590_: *mut crate::leanh::LeanObject,
    mut v___y_7591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7592_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_7587_, v_f_7588_, v_init_7589_, v___y_7590_);
    crate::leanh::lean_dec_ref(v___y_7590_);
    return v_res_7592_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(
    mut v_00_u03c3_7593_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7594_: *mut crate::leanh::LeanObject,
    mut v_map_7595_: *mut crate::leanh::LeanObject,
    mut v_f_7596_: *mut crate::leanh::LeanObject,
    mut v_init_7597_: *mut crate::leanh::LeanObject,
    mut v___y_7598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7600_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_7596_, v_map_7595_, v_init_7597_, v___y_7598_);
    return v___x_7600_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(
    mut v_00_u03c3_7601_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7602_: *mut crate::leanh::LeanObject,
    mut v_map_7603_: *mut crate::leanh::LeanObject,
    mut v_f_7604_: *mut crate::leanh::LeanObject,
    mut v_init_7605_: *mut crate::leanh::LeanObject,
    mut v___y_7606_: *mut crate::leanh::LeanObject,
    mut v___y_7607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7608_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_7601_, v_00_u03b2_7602_, v_map_7603_, v_f_7604_, v_init_7605_, v___y_7606_);
    crate::leanh::lean_dec_ref(v___y_7606_);
    return v_res_7608_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(
    mut v_00_u03c3_7609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7611_: *mut crate::leanh::LeanObject,
    mut v_f_7612_: *mut crate::leanh::LeanObject,
    mut v_x_7613_: *mut crate::leanh::LeanObject,
    mut v_x_7614_: *mut crate::leanh::LeanObject,
    mut v___y_7615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7617_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_7612_, v_x_7613_, v_x_7614_, v___y_7615_);
    return v___x_7617_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_7618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7620_: *mut crate::leanh::LeanObject,
    mut v_f_7621_: *mut crate::leanh::LeanObject,
    mut v_x_7622_: *mut crate::leanh::LeanObject,
    mut v_x_7623_: *mut crate::leanh::LeanObject,
    mut v___y_7624_: *mut crate::leanh::LeanObject,
    mut v___y_7625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7626_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_7618_, v_00_u03b1_7619_, v_00_u03b2_7620_, v_f_7621_, v_x_7622_, v_x_7623_, v___y_7624_);
    crate::leanh::lean_dec_ref(v___y_7624_);
    return v_res_7626_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_7627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7628_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_7629_: *mut crate::leanh::LeanObject,
    mut v_f_7630_: *mut crate::leanh::LeanObject,
    mut v_as_7631_: *mut crate::leanh::LeanObject,
    mut v_i_7632_: usize,
    mut v_stop_7633_: usize,
    mut v_b_7634_: *mut crate::leanh::LeanObject,
    mut v___y_7635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7630_, v_as_7631_, v_i_7632_, v_stop_7633_, v_b_7634_, v___y_7635_);
    return v___x_7637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_7638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7639_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_7640_: *mut crate::leanh::LeanObject,
    mut v_f_7641_: *mut crate::leanh::LeanObject,
    mut v_as_7642_: *mut crate::leanh::LeanObject,
    mut v_i_7643_: *mut crate::leanh::LeanObject,
    mut v_stop_7644_: *mut crate::leanh::LeanObject,
    mut v_b_7645_: *mut crate::leanh::LeanObject,
    mut v___y_7646_: *mut crate::leanh::LeanObject,
    mut v___y_7647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7648_: usize = 0;
    let mut v_stop_boxed_7649_: usize = 0;
    let mut v_res_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7648_ = crate::leanh::lean_unbox_usize(v_i_7643_);
    crate::leanh::lean_dec(v_i_7643_);
    v_stop_boxed_7649_ = crate::leanh::lean_unbox_usize(v_stop_7644_);
    crate::leanh::lean_dec(v_stop_7644_);
    v_res_7650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_7638_, v_00_u03b2_7639_, v_00_u03c3_7640_, v_f_7641_, v_as_7642_, v_i_boxed_7648_, v_stop_boxed_7649_, v_b_7645_, v___y_7646_);
    crate::leanh::lean_dec_ref(v___y_7646_);
    crate::leanh::lean_dec_ref(v_as_7642_);
    return v_res_7650_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03c3_7651_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7652_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7653_: *mut crate::leanh::LeanObject,
    mut v_f_7654_: *mut crate::leanh::LeanObject,
    mut v_keys_7655_: *mut crate::leanh::LeanObject,
    mut v_vals_7656_: *mut crate::leanh::LeanObject,
    mut v_heq_7657_: *mut crate::leanh::LeanObject,
    mut v_i_7658_: *mut crate::leanh::LeanObject,
    mut v_acc_7659_: *mut crate::leanh::LeanObject,
    mut v___y_7660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7654_, v_keys_7655_, v_vals_7656_, v_i_7658_, v_acc_7659_, v___y_7660_);
    return v___x_7662_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03c3_7663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7665_: *mut crate::leanh::LeanObject,
    mut v_f_7666_: *mut crate::leanh::LeanObject,
    mut v_keys_7667_: *mut crate::leanh::LeanObject,
    mut v_vals_7668_: *mut crate::leanh::LeanObject,
    mut v_heq_7669_: *mut crate::leanh::LeanObject,
    mut v_i_7670_: *mut crate::leanh::LeanObject,
    mut v_acc_7671_: *mut crate::leanh::LeanObject,
    mut v___y_7672_: *mut crate::leanh::LeanObject,
    mut v___y_7673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_7663_, v_00_u03b1_7664_, v_00_u03b2_7665_, v_f_7666_, v_keys_7667_, v_vals_7668_, v_heq_7669_, v_i_7670_, v_acc_7671_, v___y_7672_);
    crate::leanh::lean_dec_ref(v___y_7672_);
    crate::leanh::lean_dec_ref(v_vals_7668_);
    crate::leanh::lean_dec_ref(v_keys_7667_);
    return v_res_7674_;
}
pub unsafe fn l_Lean_Server_handleLspRequest(
    mut v_method_7677_: *mut crate::leanh::LeanObject,
    mut v_params_7678_: *mut crate::leanh::LeanObject,
    mut v_a_7679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7681_: u8 = 0;
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7686_: u8 = 0;
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_handle_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7698_: u8 = 0;
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_handle_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7681_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_7677_);
                if v___x_7681_ == 0 {
                    v___x_7682_ = l_Lean_Server_lookupLspRequestHandler(v_method_7677_);
                    v_a_7683_ = crate::leanh::lean_ctor_get(v___x_7682_, 0);
                    v_isSharedCheck_7698_ = (!crate::leanh::lean_is_exclusive(v___x_7682_)) as u8;
                    if v_isSharedCheck_7698_ == 0 {
                        v___x_7685_ = v___x_7682_;
                        v_isShared_7686_ = v_isSharedCheck_7698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7683_);
                        crate::leanh::lean_dec(v___x_7682_);
                        v___x_7685_ = crate::leanh::lean_box(0);
                        v_isShared_7686_ = v_isSharedCheck_7698_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7699_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_7677_);
                    if crate::leanh::lean_obj_tag(v___x_7699_) == 0 {
                        crate::leanh::lean_dec(v_params_7678_);
                        v___x_7700_ = l_Lean_Server_handleLspRequest___closed__0;
                        v___x_7701_ = lean_string_append(v___x_7700_, v_method_7677_);
                        v___x_7702_ = l_Lean_Server_handleLspRequest___closed__1;
                        v___x_7703_ = lean_string_append(v___x_7701_, v___x_7702_);
                        v___x_7704_ = l_Lean_Server_RequestError_internalError(v___x_7703_);
                        v___x_7705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7705_, 0, v___x_7704_);
                        return v___x_7705_;
                    } else {
                        v_val_7706_ = crate::leanh::lean_ctor_get(v___x_7699_, 0);
                        crate::leanh::lean_inc(v_val_7706_);
                        crate::leanh::lean_dec_ref_known(v___x_7699_, 1);
                        v_handle_7707_ = crate::leanh::lean_ctor_get(v_val_7706_, 2);
                        crate::leanh::lean_inc_ref(v_handle_7707_);
                        crate::leanh::lean_dec(v_val_7706_);
                        crate::leanh::lean_inc_ref(v_a_7679_);
                        v___x_7708_ = crate::leanh::lean_apply_3(
                            v_handle_7707_,
                            v_params_7678_,
                            v_a_7679_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_7708_;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7683_) == 0 {
                    crate::leanh::lean_dec(v_params_7678_);
                    v___x_7687_ = l_Lean_Server_handleLspRequest___closed__0;
                    v___x_7688_ = lean_string_append(v___x_7687_, v_method_7677_);
                    v___x_7689_ = l_Lean_Server_handleLspRequest___closed__1;
                    v___x_7690_ = lean_string_append(v___x_7688_, v___x_7689_);
                    v___x_7691_ = l_Lean_Server_RequestError_internalError(v___x_7690_);
                    if v_isShared_7686_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7685_, 1);
                        crate::leanh::lean_ctor_set(v___x_7685_, 0, v___x_7691_);
                        v___x_7693_ = v___x_7685_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 0, v___x_7691_);
                        v___x_7693_ = v_reuseFailAlloc_7694_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7685_);
                    v_val_7695_ = crate::leanh::lean_ctor_get(v_a_7683_, 0);
                    crate::leanh::lean_inc(v_val_7695_);
                    crate::leanh::lean_dec_ref_known(v_a_7683_, 1);
                    v_handle_7696_ = crate::leanh::lean_ctor_get(v_val_7695_, 1);
                    crate::leanh::lean_inc_ref(v_handle_7696_);
                    crate::leanh::lean_dec(v_val_7695_);
                    crate::leanh::lean_inc_ref(v_a_7679_);
                    v___x_7697_ = crate::leanh::lean_apply_3(
                        v_handle_7696_,
                        v_params_7678_,
                        v_a_7679_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_7697_;
                }
            }
            2 => {
                return v___x_7693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleLspRequest___boxed(
    mut v_method_7709_: *mut crate::leanh::LeanObject,
    mut v_params_7710_: *mut crate::leanh::LeanObject,
    mut v_a_7711_: *mut crate::leanh::LeanObject,
    mut v_a_7712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7713_ = l_Lean_Server_handleLspRequest(v_method_7709_, v_params_7710_, v_a_7711_);
    crate::leanh::lean_dec_ref(v_a_7711_);
    crate::leanh::lean_dec_ref(v_method_7709_);
    return v_res_7713_;
}
pub unsafe fn l_Lean_Server_routeLspRequest(
    mut v_method_7714_: *mut crate::leanh::LeanObject,
    mut v_params_7715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7717_: u8 = 0;
    let mut v___x_7718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7722_: u8 = 0;
    let mut v___x_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileSource_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v___x_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7742_: u8 = 0;
    let mut v_fileSource_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7717_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_7714_);
                if v___x_7717_ == 0 {
                    v___x_7718_ = l_Lean_Server_lookupLspRequestHandler(v_method_7714_);
                    v_a_7719_ = crate::leanh::lean_ctor_get(v___x_7718_, 0);
                    v_isSharedCheck_7734_ = (!crate::leanh::lean_is_exclusive(v___x_7718_)) as u8;
                    if v_isSharedCheck_7734_ == 0 {
                        v___x_7721_ = v___x_7718_;
                        v_isShared_7722_ = v_isSharedCheck_7734_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7719_);
                        crate::leanh::lean_dec(v___x_7718_);
                        v___x_7721_ = crate::leanh::lean_box(0);
                        v_isShared_7722_ = v_isSharedCheck_7734_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7735_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_7714_);
                    if crate::leanh::lean_obj_tag(v___x_7735_) == 0 {
                        crate::leanh::lean_dec(v_params_7715_);
                        v___x_7736_ = l_Lean_Server_RequestError_methodNotFound(v_method_7714_);
                        v___x_7737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7737_, 0, v___x_7736_);
                        v___x_7738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7738_, 0, v___x_7737_);
                        return v___x_7738_;
                    } else {
                        v_val_7739_ = crate::leanh::lean_ctor_get(v___x_7735_, 0);
                        v_isSharedCheck_7748_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7735_)) as u8;
                        if v_isSharedCheck_7748_ == 0 {
                            v___x_7741_ = v___x_7735_;
                            v_isShared_7742_ = v_isSharedCheck_7748_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_7739_);
                            crate::leanh::lean_dec(v___x_7735_);
                            v___x_7741_ = crate::leanh::lean_box(0);
                            v_isShared_7742_ = v_isSharedCheck_7748_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7719_) == 0 {
                    crate::leanh::lean_dec(v_params_7715_);
                    v___x_7723_ = l_Lean_Server_RequestError_methodNotFound(v_method_7714_);
                    v___x_7724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7724_, 0, v___x_7723_);
                    if v_isShared_7722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7721_, 0, v___x_7724_);
                        v___x_7726_ = v___x_7721_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7727_, 0, v___x_7724_);
                        v___x_7726_ = v_reuseFailAlloc_7727_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_7728_ = crate::leanh::lean_ctor_get(v_a_7719_, 0);
                    crate::leanh::lean_inc(v_val_7728_);
                    crate::leanh::lean_dec_ref_known(v_a_7719_, 1);
                    v_fileSource_7729_ = crate::leanh::lean_ctor_get(v_val_7728_, 0);
                    crate::leanh::lean_inc_ref(v_fileSource_7729_);
                    crate::leanh::lean_dec(v_val_7728_);
                    v___x_7730_ = crate::leanh::lean_apply_1(v_fileSource_7729_, v_params_7715_);
                    if v_isShared_7722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7721_, 0, v___x_7730_);
                        v___x_7732_ = v___x_7721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7733_, 0, v___x_7730_);
                        v___x_7732_ = v_reuseFailAlloc_7733_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7726_;
            }
            3 => {
                return v___x_7732_;
            }
            4 => {
                v_fileSource_7743_ = crate::leanh::lean_ctor_get(v_val_7739_, 0);
                crate::leanh::lean_inc_ref(v_fileSource_7743_);
                crate::leanh::lean_dec(v_val_7739_);
                v___x_7744_ = crate::leanh::lean_apply_1(v_fileSource_7743_, v_params_7715_);
                if v_isShared_7742_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7741_, 0);
                    crate::leanh::lean_ctor_set(v___x_7741_, 0, v___x_7744_);
                    v___x_7746_ = v___x_7741_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7747_, 0, v___x_7744_);
                    v___x_7746_ = v_reuseFailAlloc_7747_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_routeLspRequest___boxed(
    mut v_method_7749_: *mut crate::leanh::LeanObject,
    mut v_params_7750_: *mut crate::leanh::LeanObject,
    mut v_a_7751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7752_ = l_Lean_Server_routeLspRequest(v_method_7749_, v_params_7750_);
    crate::leanh::lean_dec_ref(v_method_7749_);
    return v_res_7752_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Requests(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileSource(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_requestHandlers = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_requestHandlers);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_statefulRequestHandlers = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_statefulRequestHandlers);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Requests(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Requests(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_RequestCancellation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_FileSource(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_FileWorker_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Requests(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Requests(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Requests(builtin);
}
